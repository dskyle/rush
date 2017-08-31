use std::rc::Rc;
use std::cell::{RefCell};
use std::ops::{Deref};
use val::Val;
use std::fmt::{Formatter, Debug, Error};

pub trait Resolver {
    fn get(&self, name: &str) -> Option<&VarRef>;

    fn set(&self, name: &str, val: Val) -> bool {
        if let Some(r) = self.get(name) {
            r.set(val);
            true
        } else {
            false
        }
    }
}

pub trait VarOps {
    fn get(&self) -> Val;
    fn set(&self, Val);
    fn ops_clone(&self) -> Box<VarOps>;

    /// Take and return value of variable; replace with ()
    fn take(&self) -> Val {
        let ret = self.get();
        self.set(Val::void());
        ret
    }

}

#[derive(Clone)]
struct DebugOps {
    val: RefCell<Val>,
}

impl VarOps for DebugOps {
    fn get(&self) -> Val {
        eprintln!("Reading {:?}", self.val);
        self.val.borrow().clone()
    }

    fn set(&self, val: Val) {
        eprintln!("Writing {:?}", val);
        *self.val.borrow_mut() = val;
    }

    fn ops_clone(&self) -> Box<VarOps> { Box::new(self.clone()) }
}

#[derive(Clone)]
pub struct EnvOps {
    name: String,
    delim: Option<char>,
}

impl EnvOps {
    pub fn new<S: Into<String>>(name: S, delim: Option<char>) -> EnvOps {
        EnvOps{name: name.into(), delim: delim}
    }
}

impl VarOps for EnvOps {
    fn get(&self) -> Val {
        use std::env::{var};

        match var(&self.name) {
            Ok(val) => {
                match self.delim {
                    Some(delim) => {
                        let parts = if delim == ' ' {
                            val.split_whitespace().map(|x| Val::str(x)).collect()
                        } else {
                            val.split(delim).map(|x| Val::str(x)).collect()
                        };
                        Val::Tup(parts)
                    },
                    None => Val::str(val)
                }
            },
            Err(err) => {
                Val::err_string(format!("Error getting environment variable {:?}: {:?}", self.name, err))
            },
        }
    }

    fn set(&self, val: Val) {
        use std::env::{set_var};

        set_var(&self.name, val.flat_join(self.delim).get_str().unwrap());

    }

    fn ops_clone(&self) -> Box<VarOps> { Box::new(self.clone()) }
}

impl Clone for Box<VarOps> {
    fn clone(&self) -> Self {
        self.ops_clone()
    }
}

#[derive(Clone)]
pub enum Variable {
    Value(RefCell<Val>),
    Ops(Box<VarOps>),
}

impl Debug for Variable {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "Variable(val: {:?})", self.get())
    }
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self as *const Variable == other as *const Variable
    }
}

impl Variable {
    fn new(val: Val) -> Variable {
        Variable::Value(RefCell::new(val))
    }

    fn using<O: 'static + VarOps>(ops: O) -> Variable {
        Variable::Ops(Box::new(ops))
    }

    pub fn set(&self, val: Val) {
        match *self {
            Variable::Value(ref cell) => *cell.borrow_mut() = val,
            Variable::Ops(ref hooks) => hooks.set(val),
        }
    }

    pub fn get(&self) -> Val {
        match *self {
            Variable::Value(ref cell) => cell.borrow().clone(),
            Variable::Ops(ref hooks) => hooks.get(),
        }
    }

    pub fn with_ref<T, F: FnOnce(&Val) -> T> (&self, f: F) -> T {
        match *self {
            Variable::Value(ref cell) => f(&*cell.borrow()),
            Variable::Ops(ref hooks) => {
                let val = hooks.get();
                f(&val)
            },
        }
    }

    pub fn with_mut<T, F: FnOnce(&mut Val) -> T> (&self, f: F) -> T {
        match *self {
            Variable::Value(ref cell) => f(&mut *cell.borrow_mut()),
            Variable::Ops(ref hooks) => {
                let mut val = hooks.get();
                let ret = f(&mut val);
                hooks.set(val);
                ret
            },
        }
    }

    /// Take and return value of variable; replace with ()
    pub fn take(&self) -> Val {
        match *self {
            Variable::Value(ref cell) => {
                let mut r = cell.borrow_mut();
                let mut tmp = Val::void();

                use std::ops::DerefMut;
                ::std::mem::swap(&mut tmp, r.deref_mut());

                return tmp;
            },
            Variable::Ops(ref hooks) => hooks.take(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarRef {
    rc: Rc<Variable>,
}

impl VarRef {
    pub fn new(val: Val) -> VarRef {
        VarRef{rc: Rc::new(Variable::new(val))}
    }

    pub fn using<O: 'static + VarOps>(ops: O) -> VarRef {
        VarRef{rc: Rc::new(Variable::using(ops))}
    }
}

impl Deref for VarRef {
    type Target = Variable;

    fn deref(&self) -> &Self::Target {
        &self.rc
    }
}

pub trait Binder {
    fn import<T: Into<String>>(&mut self, name: T, var: VarRef) -> &VarRef;

    fn bind<T: Into<String>>(&mut self, name: T, val: Val) -> &VarRef {
        self.import(name, VarRef::new(val))
    }
}

pub trait Scoped {
    fn enter_scope(&mut self);
    fn exit_scope(&mut self);
}

pub struct LocalVars {
    vars: Vec<(String, VarRef)>,
    scopes: Vec<usize>,
}

impl LocalVars {
    pub fn new() -> LocalVars {
        LocalVars{vars: vec![], scopes: vec![0]}
    }

    pub fn last(&self) -> Option<&VarRef> {
        self.vars.last().map(|x| &x.1)
    }
}

impl Resolver for LocalVars {
    fn get(&self, name: &str) -> Option<&VarRef> {
        self.vars.iter().rev().find(|&cur| cur.0 == name).map(|ref x| &x.1)
    }
}

impl Binder for LocalVars {
    fn import<T: Into<String>>(&mut self, name: T, var: VarRef) -> &VarRef{
        self.vars.push((name.into(), var));
        let scope: &mut usize = self.scopes.last_mut().unwrap();
        *scope += 1;
        &self.vars.last().unwrap().1
    }
}

impl Scoped for LocalVars {
    fn enter_scope(&mut self) {
        self.scopes.push(0)
    }

    fn exit_scope(&mut self) {
        if let Some(l) = self.scopes.pop() {
            for x in self.vars.iter().rev().take(l) {
                x.1.with_ref(|x| x.unhandled());
            }
            let len = self.vars.len() - l;
            self.vars.truncate(len)
        }
    }
}

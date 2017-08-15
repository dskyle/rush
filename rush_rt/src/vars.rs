use std::rc::Rc;
use std::cell::{RefCell, RefMut, Ref};
use std::ops::Deref;
use val::Val;

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

#[derive(Debug, Clone, PartialEq)]
pub struct Variable {
    val: RefCell<Val>,
}

impl Variable {
    fn new(val: Val) -> Variable {
        Variable{val: RefCell::new(val)}
    }

    pub fn set(&self, val: Val) {
        *self.val.borrow_mut() = val
    }

    pub fn get(&self) -> Val {
        self.val.borrow().clone()
    }

    pub fn get_ref(&self) -> Ref<Val> {
        self.val.borrow()
    }

    pub fn get_mut(&self) -> RefMut<Val> {
        self.val.borrow_mut()
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
                x.1.get_ref().unhandled();
            }
            let len = self.vars.len() - l;
            self.vars.truncate(len)
        }
    }
}

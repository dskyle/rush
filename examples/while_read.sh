x="x"
ls | while read l; do
  echo found $l
  x="$x x"
done
echo $x

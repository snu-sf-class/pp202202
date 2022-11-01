class A {
  a
  b
  f
  g = ... f ...
  h = ... f ...
}

class B(arg) extends A(arg+1) {
  x
  y
  override f
}

-------------------

trait AI {
  g
  h
}
class A(_of) extends AI {
  a
  b
  f = _of match Some _f => _f | None => ((x) => ... )
  g = ... f ...
  h = ... f ...
}
class B(arg) extends AI {
  p = new A(Some((x) => ...))
  g = p.g
  h = p.h

  x
  y
}

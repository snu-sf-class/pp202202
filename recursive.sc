

{
trait AI[X] {
  def f(x: X): Int
}

trait BI[Y] {
  def g(y: Y): Int
}

implicit def aimp(implicit bi: => BI[Int]) : AI[Int] = new AI[Int] {
  def f(x: Int): Int =
    if (x > 0) bi.g(x-1) else 42
}

implicit def bimp(implicit ai: => AI[Int]) : BI[Int] = new BI[Int] {
  def g(y: Int): Int =
    ai.f(y)
}

def test(implicit ai: AI[Int]) = ai.f(100)

/*
def aimp_instance : AI[Int] = aimp(bimp_instance)
def bimp_instance : BI[Int] = bimp(aimp_instance)
test(aimp_instance)
*/

test
}




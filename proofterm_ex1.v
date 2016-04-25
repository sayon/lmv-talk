Definition t1 : (A -> B -> C) -> A -> B -> C  :=
  fun f: A-> B-> C =>
    fun a: A  =>
      fun b: B =>
        f a b.

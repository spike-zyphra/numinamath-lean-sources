import Mathlib

-- All points in {0,1}^3
def allPoints : List (Fin 2 × Fin 2 × Fin 2) :=
  List.product (List.ofFn id) (List.product (List.ofFn id) (List.ofFn id))
  |>.map (fun (a, (b, c)) => (a, b, c))

-- Check whether a ≥ b holds in each coordinate
def gePoint (a b : Fin 2 × Fin 2 × Fin 2) : Bool :=
  a.1.val ≥ b.1.val && a.2.1.val ≥ b.2.1.val && a.2.2.val ≥ b.2.2.val

-- Check whether the function satisfies the monotonicity condition
def isMonotone (f : (Fin 2 × Fin 2 × Fin 2) → Bool) : Bool :=
  allPoints.all (fun a =>
    allPoints.all (fun b =>
      if gePoint a b then
        (!f a || f b)  -- i.e., f(a) ≥ f(b)
      else
        true
    )
  )

-- All 2^8 = 256 Boolean functions f: {0,1}^3 → {0,1}
def allBoolFuncs : List ((Fin 2 × Fin 2 × Fin 2) → Bool) :=
  let bools := (List.range (2^8)).map (fun n =>
    (List.range 8).map (fun i => ((n >>> (7 - i)) &&& 1) == 1))  -- Generate 8-bit truth tables
  bools.map (fun bits =>
    fun (x : Fin 2 × Fin 2 × Fin 2) =>
      let idx := List.findIdx (· == x) allPoints 
      bits[idx]!
  )

/- How many functions $f:\{0,1\}^{3} \rightarrow\{0,1\}$ satisfy the property that, for all ordered triples $\left(a_{1}, a_{2}, a_{3}\right)$ and $\left(b_{1}, b_{2}, b_{3}\right)$ such that $a_{i} \geq b_{i}$ for all $i, f\left(a_{1}, a_{2}, a_{3}\right) \geq f\left(b_{1}, b_{2}, b_{3}\right)$ ?-/
theorem number_theory_609596 : (allBoolFuncs.filter isMonotone).length = 20 := by
  native_decide

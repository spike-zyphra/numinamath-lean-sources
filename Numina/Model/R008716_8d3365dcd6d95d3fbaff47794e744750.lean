import Mathlib

theorem algebra_19515 {f g p q : ℝ → ℝ}
    (hf : f = fun x => x + 5) (hg : g = fun x => x ^ 2 + 1)
    (hp : p = fun x => g x + f x) (hq : q = fun x => g x - f x) :
    p * q = fun x => (x ^ 4 + x ^ 2 - 10 * x - 24) := by
  funext x
  simp [hp, hq, hg, hf]
  ring
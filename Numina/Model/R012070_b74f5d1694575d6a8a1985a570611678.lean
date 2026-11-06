import Mathlib

/- f is the function defined in the problem, it takes a tuple of three integers and returns a tuple of three integers. -/
def f : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
| (x, y, z) => (y + z - x, z + x - y, x + y - z)

/- Let's define a sequence q that will be used to express the iterated function f^[n]. -/
def q : ℕ → ℤ
| 0 => 0
| n + 1 => 1 - 2 * q n

lemma lemma_1 (n : ℕ) (x y z : ℤ) :
    f^[n] (x, y, z) = (q n * y + q n * z + (1 - 2 * q n) * x, q n * z + q n * x + (1 - 2 * q n) * y, q n * x + q n * y + (1 - 2 * q n) * z) := by
  -- We can prove this by induction on n.
  induction n with
  | zero => simp [q]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, ih, q, f]
    ring_nf

lemma lemma_2 (n : ℕ) :
    3 * q n = 1 - (-2) ^ n := by
  -- We can prove this by induction on n.
  induction n with
  | zero => simp [q]
  | succ n ih =>
    simp [q, pow_succ]
    linear_combination -2 * ih

theorem number_theory_604962 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h : a + b + c = 2013) :
    let (x, y, z) := f^[10] (a, b, c);
    x < 0 ∨ y < 0 ∨ z < 0 := by 
  simp [Function.iterate_succ', f]
  <;> omega
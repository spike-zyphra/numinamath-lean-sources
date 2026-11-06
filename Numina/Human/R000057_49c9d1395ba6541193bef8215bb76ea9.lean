import Mathlib

/- f is a real-valued function on the reals satisfying
1. \( f(0) = \frac{1}{2} \),
2. for some real \( a \), we have \( f(x+y) = f(x) f(a-y) + f(y) f(a-x) \) for all \( x, y \).
Prove that \( f \) is constant.-/
theorem functional_equations_4192 {f : ℝ → ℝ} (h0 : f 0 = 1 / 2)
    (ha : ∃ a, ∀ x y, f (x + y) = f x * f (a - y) + f y * f (a - x)) :
    ∃ c, ∀ x, f x = c := by
  rcases ha with ⟨a, ha⟩
  -- assign x=0, y=0 to f(x+y)=f(x)f(a-y)+f(y)f(a-x)
  have ha00 := ha 0 0
  -- deduce f(a)=1/2 by simple calculation
  simp [h0] at ha00
  rw [← mul_add, ← two_mul, ← mul_assoc, eq_comm] at ha00
  rw [show 2⁻¹ * 2 = (1 : ℝ) by ring, one_mul] at ha00
  -- assign y=0 to f(x+y)=f(x)f(a-y)+f(y)f(a-x)
  have hax x := ha x 0
  simp [h0, ha00] at hax
  -- after simplification, we have f(x)=f(a-x)
  replace hax x : f x = f (a - x) := by
    linear_combination 2  * (hax x)
  -- assign y=a-x to f(x+y)=f(x)f(a-y)+f(y)f(a-x)
  have haxy x := ha x (a - x)
  simp [h0, ha00] at haxy
  -- after simplification, we have f(x)^2=1/4
  replace haxy x : f x ^ 2 = 1 / 4 := by
    specialize haxy x
    rw [← hax x] at haxy
    linear_combination -1/2 * haxy
  use 1 / 2
  intro x
  specialize haxy x
  rw [show (1 : ℝ)/4=(1/2)^2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at haxy
  -- from f(x)^2=1/4 we have f(x)=1/2 or f(x)=-1/2
  rcases haxy with _ | haxy
  -- f(x)=1/2 is desired
  . assumption
  -- f(x)=-1/2 is impossible, becasuse f(x) is nonneg
  exfalso
  specialize hax (x / 2)
  specialize ha (x / 2) (x / 2)
  -- deduce f(x) = f(x/2)^2 + f(x/2)^2 from ha
  rw [← hax, ← pow_two] at ha
  -- f(x) is sum of square, hence nonneg
  have : 0 ≤ f x := by
    rw [show x = x / 2 + x / 2 by ring, ha]
    apply add_nonneg <;> apply sq_nonneg
  linarith

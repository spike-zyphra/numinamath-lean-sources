import Mathlib
open Polynomial
/- When the polynomial $p(x)$ is divided by $x - 1,$ the remainder is 3.  When the polynomial $p(x)$ is divided by $x - 3,$ the remainder is 5.  What is the remainder when the polynomial $p(x)$ is divided by $(x - 1)(x - 3)$?-/
theorem algebra_18897 {p : Polynomial ℝ} (h₁ : p % (X - 1) = 3) (h₂ : p % (X - 3) = 5) : p % ((X - 1) * (X - 3)) = X + 2 := by
  -- the property of remainder
  have dvd_sub_mod : ∀ (f g : ℝ[X]), g ∣ f - f % g := by intro f g; use f / g; nth_rw 1 [← EuclideanDomain.div_add_mod f g]; rw [add_sub_cancel_right]
  have d₁ := dvd_sub_mod p (X - 1) --Using the property of remainder
  have d₂ := dvd_sub_mod p (X - 3) --Using the property of remainder
  rw [h₁] at d₁
  rw [h₂] at d₂
  have d₃ := mul_dvd_mul_right d₁ (X - 3) --Multiply by X - 3 on the each side of d₁
  have d₄ := mul_dvd_mul_left (X - 1) d₂ --Multiply by X - 1 on the each side of d₂
  have d₅ := dvd_sub d₄ d₃ --Substract d₃ and d₄
  have e₁ : (2 : ℝ[X]) = C (2 : ℝ) := rfl
  have e₂ : (3 : ℝ[X]) = C (3 : ℝ) := rfl
  have e₃ : (1 : ℝ[X]) = C (1 : ℝ) := rfl
  have : (X - 1) * (p - 5) - (p - 3) * (X - 3) = (p - (X + 2)) * (C 2) := by rw [← e₁]; ring
  rw [this] at d₅
  have h₆ := dvd_mul_of_dvd_left d₅ (C 2⁻¹)
  rw [mul_assoc, ← C_mul] at h₆
  simp at h₆
  have aux: ∀ {f g k : ℝ[X]}, f ∣ g - k → k.degree < f.degree → g % f = k := by
    intro f g k h₁ h₂
    have d₁ := dvd_sub h₁ (dvd_sub_mod g f)
    have : g - k - (g - g % f) = g % f - k := by ring
    rw [this] at d₁
    have fnz := ne_zero_of_degree_gt h₂
    have := EuclideanDomain.mod_lt g fnz
    have aux₁ : ∀ (p q : ℝ[X]), (EuclideanDomain.r p q) = (p.degree < q.degree) := fun p q ↦ rfl
    rw [aux₁] at this
    rcases d₁ with ⟨q, hq⟩
    by_cases qz : q = 0
    · rw [qz, mul_zero, sub_eq_zero] at hq
      exact hq
    have qd := zero_le_degree_iff.mpr qz
    have h₃ := congr_arg degree hq
    rw [degree_mul] at h₃
    have h₄ := degree_sub_le (g % f) k
    have h₅ := max_lt_iff.mpr ⟨this, h₂⟩
    have h₆ := add_le_add_left qd f.degree
    rw [add_zero, ← h₃] at h₆
    exfalso
    have := lt_of_le_of_lt (le_trans h₆ h₄) h₅
    exact ne_of_lt this rfl
  apply aux h₆
  rw [e₁, e₂, e₃, degree_X_add_C, degree_mul, degree_X_sub_C, degree_X_sub_C]
  norm_num
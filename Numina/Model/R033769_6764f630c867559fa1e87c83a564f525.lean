import Mathlib

theorem algebra_21500 {a b c : ℂ} (h₀ : (a + 1) * (b + 1) * (c + 1) = 1)
    (h₁ : (a + 2) * (b + 2) * (c + 2) = 2) (h₂ : (a + 3) * (b + 3) * (c + 3) = 3) :
    (a + 4) * (b + 4) * (c + 4) = 10 := by 
  have eq1 : a * b * c + (a * b + a * c + b * c) + (a + b + c) = 0 := by
    have h := h₀
    ring_nf at h ⊢
    simp [Complex.ext_iff] at h ⊢
    constructor <;> linarith
  have eq2 : a * b * c + 2 * (a * b + a * c + b * c) + 4 * (a + b + c) = -6 := by
    have h := h₁
    ring_nf at h ⊢
    simp [Complex.ext_iff] at h ⊢
    constructor <;> linarith
  have eq3 : a * b * c + 3 * (a * b + a * c + b * c) + 9 * (a + b + c) = -24 := by
    have h := h₂
    ring_nf at h ⊢
    simp [Complex.ext_iff] at h ⊢
    constructor <;> linarith
  have eq4 : (a * b + a * c + b * c) + 3 * (a + b + c) = -6 := by 
    have eq4 := eq2
    have eq5 := eq1
    ring_nf at eq4 eq5 ⊢
    simp [Complex.ext_iff] at eq4 eq5 ⊢
    constructor <;> linarith
  have eq5 : (a * b + a * c + b * c) + 5 * (a + b + c) = -18 := by 
    have eq6 := eq3
    have eq7 := eq2
    ring_nf at eq6 eq7 ⊢
    simp [Complex.ext_iff] at eq6 eq7 ⊢
    constructor <;> linarith
  have eq6 : a + b + c = -6 := by
    have eq7 := eq5
    have eq8 := eq4
    ring_nf at eq7 eq8 ⊢
    simp [Complex.ext_iff] at eq7 eq8 ⊢
    constructor <;> linarith
  have eq7 : a * b + a * c + b * c = 12 := by
    rw [eq6] at eq4
    simp [Complex.ext_iff] at eq4 ⊢
    constructor <;> linarith
  have eq8 : a * b * c = -6 := by
    have eq9 := eq1
    rw [eq7, eq6] at eq9
    simp [Complex.ext_iff] at eq9 ⊢
    constructor <;> linarith
  have eq9 : (a + 4) * (b + 4) * (c + 4) = a * b * c + 4 * (a * b + a * c + b * c) + 16 * (a + b + c) + 64 := by
    ring
  rw [eq9]
  rw [eq8, eq7, eq6]
  all_goals
    simp [Complex.ext_iff]
    <;> norm_num
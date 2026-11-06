import Mathlib

theorem algebra_312343 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : ∃! x : ℝ, a * x ^ 2 + b * x + c = 0 ∧ b * x ^ 2 + c * x + a = 0 ∧
      c * x ^ 2 + a * x + b = 0) :
    a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = 3 := by
  rcases h with ⟨r, hr, hr_unique⟩
  rcases hr with ⟨hr₁, hr₂, hr₃⟩
  -- Summing the three equations
  have h_sum : (a + b + c) * (r ^ 2 + r + 1) = 0 := by
    nlinarith 
  -- showing r^2+r+1≠0 real polynomial minimum value >0
  have h_neq : r^2 + r + 1 ≠ 0 := by 
    nlinarith [sq_nonneg (r + 1/2)]
  have h1 : a + b + c = 0 := by 
    apply_fun (fun x => x / (r^2 + r + 1)) at h_sum
    field_simp [h_neq] at h_sum ⊢
    all_goals nlinarith [h_sum]
  have h2 : a^3 + b^3 + c^3 = 3 * a * b * c := by
    have h1' : a + b + c = 0 := h1
    have h_eq : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a*b + a*c + b*c)) := by ring
    rw [h1'] at h_eq
    linarith [h_eq]
  have h_eq1 : a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) =
    (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) := by
    field_simp
    <;> ring
  rw [h_eq1]
  have h3 : a ^ 3 + b ^ 3 + c^3 = 3 * (a * b * c) := by
    linarith [h2]
  rw [h3]
  field_simp
  <;> ring_nf <;> norm_num
  <;> nlinarith <;> tauto
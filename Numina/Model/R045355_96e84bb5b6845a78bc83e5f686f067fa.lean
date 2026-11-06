import Mathlib

theorem algebra_9218 (f : ℝ → ℝ) (m : ℝ) (α β : ℝ) (h₀ : α^2 - m * α - 1 = 0) (h₁ : β^2 - m * β - 1 = 0)
    (h₂ : α < β) (h₃ : f = fun x => (2 * x - m) / (x^2 + 1)) :
    (∀ x ∈ Set.Ioo α β, deriv f x > 0) := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  rw [h₃]
  have h4 : deriv (fun (y : ℝ) => (2 * y - m) / (y ^ 2 + 1)) x =
    (2 * (x^2 + 1) - (2 * x - m) * (2 * x)) / (x^2 + 1)^2 := by
    simp [deriv_div, deriv_add, deriv_sub, deriv_const, mul_comm]
    <;> field_simp
    <;> ring
    <;> norm_num
  rw [h4]
  have h7 : (x : ℝ) ^ 2 - m * x - 1 < 0 := by
    have h12 : α ^ 2 - m * α - 1 = 0 := h₀
    have h13 : β ^ 2 - m * β - 1 = 0 := h₁
    have h14 : (x : ℝ) ^ 2 - m * x - 1 = (x - α) * (x - β) := by
      have h15 : m = α + β := by
        nlinarith
      rw [h15]
      nlinarith [sq_pos_of_pos (sub_pos.mpr h₂), sq_nonneg (x - α), sq_nonneg (x - β)]
    rw [h14]
    have h15 : (x - α) * (x - β) < 0 := by
      apply mul_neg_of_pos_of_neg
      · linarith
      · linarith
    linarith
  have h14 : 2 * (x ^ 2 + 1) - (2 * x - m) * (2 * x) > 0 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr h₂), sq_nonneg (x - α), sq_nonneg (x - β)]
  have h8 : (x ^ 2 + 1) ^ 2 > 0 := by
    positivity
  apply div_pos
  · linarith
  · nlinarith
import Mathlib

/- Given that $log_{10}(\sin(x)) + log_{10}(\cos(x)) = -1$ and
$log_{10}(\sin(x) + \cos(x)) = \frac{1}{2} (log_{10}(n) - 1)$, find $n$. -/
theorem algebra_98145 {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (n : ℝ)
(hn : n > 0)
(h₁ : Real.logb 10 (Real.sin x) + Real.logb 10 (Real.cos x) = -1)
(h₂ : Real.logb 10 (Real.sin x + Real.cos x) = (Real.logb 10 n - 1) / 2) :
n = 12 := by
  simp at hx
  -- First show sin x, cos x are positive
  have hsin : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have hcos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    simp
    exact ⟨by linarith, by linarith⟩
  -- Simplify the first equation
  rw [← Real.logb_mul (by linarith) (by linarith),
      Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by apply mul_pos <;> linarith)
  ] at h₁
  -- Simplify second equation
  field_simp at h₂
  rw [mul_comm] at h₂
  have h₃ : 2* Real.logb 10 (Real.sin x + Real.cos x) = Real.logb 10 ((Real.sin x + Real.cos x)^2) := by
    simp [Real.logb_pow]
  rw [h₃,
      Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by apply sq_pos_iff.mpr; linarith),
      Real.rpow_sub (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hn,
  ] at h₂
  ring_nf at h₂
  -- sin^2+cos^2 = 1
  rw [add_assoc, Real.sin_sq_add_cos_sq] at h₂
  -- substitude first equation
  rw [← h₁] at h₂
  -- now it's trivial
  linarith
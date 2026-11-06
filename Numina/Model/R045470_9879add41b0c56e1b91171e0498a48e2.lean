import Mathlib

theorem algebra_13636 {dom: Set ℝ} {f : ℝ → ℝ}
    (hd: ∀x∈dom, 1/x ∈dom) (hf : ∀x∈dom, f x + f (1/x) = x)
    (h : 0 ∉ dom) : (∀x∈dom, x = -1 ∨ x = 1) := by
  intro x hx
  have hx1 : 1 / x ∈ dom := hd x hx
  have h1 := hf x hx
  have h2 := hf (1 / x) hx1
  have hx2 : x ≠ 0 := by
    intro hx0
    have h0 : (0 : ℝ) ∈ dom := by
      rw [hx0] at hx
      exact hx
    contradiction
  have hx3 : 1 / (1 / x) = x := by
    field_simp [hx2]
  have eq1 := h2
  have eq2 : f x + f (1 / x) = x := by 
    simpa using h1
  -- eq1 : f (1/x) + f x =1/x
  simp [show 1 / (1 / x) = x by 
      field_simp [hx2]
    ] at eq1 
  have eq3 : f (1 / x) + f x = 1 / x := by 
    simpa using eq1
  have eq4 : x = 1 / x := by
    nlinarith 
  have hx5 : x ^ 2 = 1 := by 
    field_simp [hx2] at eq4 
    nlinarith 
  have hx6 : x = 1 ∨ x = -1 := by 
    rw [sq_eq_one_iff] at hx5
    tauto
  tauto
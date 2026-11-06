import Mathlib

theorem algebra_273522 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h1 : ∀ x, f (x - 4) = f (2 - x)) (h2 : ∀ x, f x ≥ x)
    (h3 : IsLeast (Set.range f) 0)
    (h4 : ∀ x ∈ Set.Ioo 0 2, f x ≤ ((x + 1) / 2) ^ 2) :
    f = fun x => (1 / 4) * (x + 1) ^ 2 := by
  rcases hf with ⟨a, b, c, h_def⟩
  have h11 := h1 0
  simp [h_def] at h11
  have h12 : b = 2 * a := by
    nlinarith
  have h6 : 0 ∈ Set.range f := h3.1
  rcases h6 with ⟨x, hx⟩
  have h7 : ∀ y ∈ Set.range f, 0 ≤ y := by
    apply h3.2
  have hx' : f x = 0 := by
    linarith
  simp [h_def] at hx'
  have eq1 := h4 1 (by norm_num)
  norm_num [h_def] at eq1
  have eq2 := h2 1
  norm_num [h_def] at eq2
  have eq3 := h2 0
  norm_num [h_def] at eq3
  have eq4 := h2 2
  norm_num [h_def] at eq4
  have eq5 := h2 3
  norm_num [h_def] at eq5
  have eq6 := h2 (-2)
  norm_num [h_def] at eq6
  have eq7 := h4 0.5 (by norm_num)
  norm_num [h_def] at eq7
  have eq8 := h4 1.5 (by norm_num)
  norm_num [h_def] at eq8
  funext x
  simp [h_def]
  have eq9 : a = 1 / 4 := by
    nlinarith [h12, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8]
  have eq10 : b = 1 / 2 := by
    linarith [h12, eq9]
  have eq11 : c = 1 / 4 := by
    nlinarith [eq1, eq9, eq10]
  simp [eq9, eq10, eq11]
  <;> ring
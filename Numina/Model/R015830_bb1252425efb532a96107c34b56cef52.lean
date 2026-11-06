import Mathlib

theorem algebra_126286 (a b c : ℚ) (h : ∀ x : ℤ, ∃ n : ℤ, a * x ^ 2 + b * x + c = n) :
    (∃ m n p : ℤ, 2 * a = m ∧ a + b = n ∧ c = p) ∧
    (∀ m n p : ℤ, 2 * a = m ∧ a + b = n ∧ c = p →
      (∀ x : ℤ, ∃ n : ℤ, a * x ^ 2 + b * x + c = n)) := by
  constructor
  · 
    have h1 := h 0
    rcases h1 with ⟨n0, hn0⟩
    have hc1 : c = (n0 : ℚ) := by
      norm_num at hn0
      linarith
    have h2 := h 1
    rcases h2 with ⟨n1, hn1⟩
    have h3 := h (-1)
    rcases h3 with ⟨n_1, hn_1⟩
    have ha1d : ∃ m : ℤ, 2 * a = (m : ℚ) := by
      have hc2 : c = (n0 : ℚ) := hc1
      have ha2a : 2 * a = (n1 + n_1 : ℚ) - 2 * (c : ℚ) := by
        norm_num at hn1 hn_1
        linarith
      rw [hc2] at ha2a
      refine ⟨n1 + n_1 - 2 * n0, by simp_all⟩
    rcases ha1d with ⟨m, hm⟩
    have hn4 : ∃ n : ℤ, a + b = (n : ℚ) := by
      have hc2 : c = (n0 : ℚ) := hc1
      have ha2a : a + b = (n1 : ℚ) - c := by
        norm_num at hn1
        linarith
      rw [hc2] at ha2a
      refine ⟨n1 - n0, by simp_all⟩
    rcases hn4 with  ⟨n, hn⟩
    have hc2 : ∃ p : ℤ, c = (p : ℚ) := by
      refine ⟨n0, by linarith [hc1]⟩
    rcases hc2 with ⟨p, hp⟩
    exact ⟨m, n, p, hm, hn, hp⟩
  · 
    intro m n p h9
    intro x
    have h10 := h x
    simpa using h10
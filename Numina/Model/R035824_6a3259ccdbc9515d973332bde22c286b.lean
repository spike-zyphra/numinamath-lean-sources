import Mathlib

open Finset

theorem number_theory_29216 {d : ℤ → ℤ → ℕ}
    (hd : ∀ x y, d x y = min ((x - y) % 2553) ((y - x) % 2553)) :
    ∀ S : Set ℤ, S.encard ≥ 70 → ∃ m ∈ S, ∃ n ∈ S, d m n ≤ 36 := by
  intro S hS
  have h : S.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [Set.eq_empty_iff_forall_not_mem] at h
    have h1 : S = ∅ := Set.eq_empty_iff_forall_not_mem.mpr h
    rw [h1] at hS
    simp [Set.encard_eq_zero] at hS
  rcases h with ⟨x, hx⟩ 
  use x, hx 
  use x, hx 
  have h1 : d x x = 0 := by 
    have h12 : (↑(d x x) : ℤ) =  min ((x - x) % 2553) ((x - x) % 2553) := by
      have h13 := hd x x
      simpa using h13
    have h11' : (↑(d x x) : ℤ) = 0 := by
      rw [h12] 
      all_goals norm_num 
    have hx0 : d x x = 0 := by
      have hx0' : (↑(d x x) : ℤ) = 0 := h11'
      have h10 : (↑(d x x) : ℤ) = (d x x : ℕ) := by simp 
      omega 
    exact hx0
  rw [h1] 
  all_goals norm_num
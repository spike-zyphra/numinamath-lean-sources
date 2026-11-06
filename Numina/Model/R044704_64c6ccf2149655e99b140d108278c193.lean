import Mathlib

theorem number_theory_7794 (n : ℤ) : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^2 - z^2 = n} := by
  cases Int.even_or_odd n with
  | inl hn_even =>
    rcases hn_even with ⟨m, hm⟩
    apply Set.infinite_of_injective_forall_mem (f := λ k => (m - 2 * k^2 - 2 * k, 2 * k + 1, m - 2 * k^2 - 2 * k - 1))
    · -- Show that the function f is injective
      intro k j h
      simp [Prod.ext_iff] at h 
      linarith 
    · -- Show that all elements produced by f are in the set
      intro k 
      simp [hm]
      ring_nf 
      <;> nlinarith [sq_nonneg (k + 1 : ℤ), sq_nonneg (m : ℤ)]
  | inr hn_odd =>
    rcases hn_odd with ⟨m, hm⟩
    apply Set.infinite_of_injective_forall_mem (f := λ k => (m + 1 - 2 * k^2, 2 * k, m - 2 * k^2))
    · -- Show that the function f is injective 
      intro k j h 
      simp [Prod.ext_iff] at h 
      all_goals nlinarith 
    · -- Show that all elements produced by f are in the set
      intro k 
      simp [hm]
      ring_nf 
      <;> nlinarith [sq_nonneg (k + 1 : ℤ), sq_nonneg (m : ℤ), sq_nonneg ((k) : ℤ)]
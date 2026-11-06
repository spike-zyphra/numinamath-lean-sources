import Mathlib

/-For any integer $n$, the equation
$$x^{2}+y^{2}-z^{2}=n$$

has infinitely many integer solutions $(x, y, z)$.-/
theorem number_theory_7794 (n : ℤ) : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^2 - z^2 = n} := by 
  cases Int.even_or_odd n with
  | inl hn_even =>
    rcases hn_even with ⟨m, hm⟩
    apply Set.infinite_of_injective_forall_mem (f := λ k => (m - 2 * k^2 - 2 * k, 2 * k + 1, m - 2 * k^2 - 2 * k - 1))
    · -- Show $f$ is injective
      intro k1 k2 h
      simp [Prod.ext_iff] at h
      linarith
    · -- Show that for all $k$, $f(k) \in S$
      intro k
      simp [Prod.mk.injEq]
      ring_nf
      omega
  | inr hn_odd =>
    rcases hn_odd with ⟨m, hm⟩
    apply Set.infinite_of_injective_forall_mem (f := λ k => (m + 1 - 2 * k^2, 2 * k, m - 2 * k^2))
    · -- Show $f$ is injective
      intro k1 k2 h
      simp [Prod.ext_iff] at h
      linarith
    · -- Show that for all $k$, $f(k) \in S$
      intro k
      simp [Prod.mk.injEq]
      ring_nf
      omega
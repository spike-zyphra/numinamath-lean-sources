import Mathlib

theorem algebra_221771 :
    ∃ M : Finset ℝ, M ≠ ∅ ∧ ∀ n : ℕ, ∃ p : Polynomial ℝ, p.degree ≥ n ∧ ∀ m ∈ p.coeffs, m ∈ M ∧
      ∀ r ∈ p.roots, r ∈ M := by
  use {0, 1}
  constructor
  · -- Show M is not empty
    simp
  · -- Show the existence of the polynomial for all n
    intro n
    use Polynomial.X ^ n
    constructor
    · -- Show that the degree is at least n
      simp
      all_goals omega
    · -- Show the coefficients and roots are in M.
      intro m hm
      have h1 : m = (1 : ℝ) := by
        have h2 : m ∈ (Polynomial.X ^ n).coeffs := by
          simpa using hm
        have h3 : (Polynomial.X ^ n).coeffs = ({1} : Finset ℝ) := by
          simp [Polynomial.coeffs, Polynomial.natDegree_X_pow, Polynomial.coeff_X_pow]
          <;> try { aesop }
          <;> try { tauto }
          <;> try { norm_num }
          <;> try {native_decide}
          <;> try { tauto }
          <;> try { tauto }
          <;> try { tauto }
          all_goals try { aesop }
        rw [h3] at h2
        simp at h2 ⊢
        all_goals
          try { tauto }
          <;> try { tauto }
          <;> try { tauto }
          <;> try { tauto }
          <;> try { tauto }
        all_goals
          try { tauto }
          <;> try { tauto }
          <;> try { tauto }
          <;> try { tauto }
          <;> try { tauto }
      rw [h1]
      constructor
      · -- Show that 1 is in M
        norm_num
      · -- Show all roots are in M
        intro r hr
        have h4 : r = (0 : ℝ) := by
          simp [Polynomial.mem_roots, pow_eq_zero_iff, show (n : ℕ) ≥ 0 by omega] at hr ⊢
          all_goals
            try { linarith }
            <;> try { tauto }
            <;> try { tauto }
          all_goals
            try { tauto }
            <;> try { tauto }
            <;> try { tauto }
        rw [h4]
        norm_num
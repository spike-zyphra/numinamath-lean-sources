import Mathlib

open Real
/- 2. (This sub-question 20 points) Let $a, b, c$ be non-negative real numbers, $a+b+c=3$,

Find the maximum value of $S=\left(a^{2}-a b+b^{2}\right)\left(b^{2}-b c+c^{2}\right)\left(c^{2}-c a+a^{2}\right)$ -/
theorem algebra_292877
: IsGreatest { S | ∃ a b c:ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 3 ∧ S = (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2)} 12 := by
    unfold IsGreatest upperBounds; simp
    constructor
    -- to get 12 use 2, 1, 0
    use 2; norm_num; use 1; norm_num; use 0; norm_num
    intro lim a ha b hb c hc habc hlim; rw [hlim]; clear hlim lim
    wlog hbc: b ≥ c; specialize this a ha c hc b hb (by linarith) (by linarith); linarith [this]
    wlog hab: a ≥ b;
      · simp at hab hbc
        cases' lt_trichotomy a c with hac hac
        · specialize this b hb c hc a ha (by linarith) (by linarith) (by linarith); linarith [this]
        · cases' hac with hbc hbc
          all_goals {
            specialize this b hb a ha c hc (by linarith) (by linarith) (by linarith); linarith [this]
          }
    -- let's show b^2 - bc + c^2 ≤b^2
    have h0: b^2-b*c+c^2 ≤ b^2 := by nlinarith
    -- same for c, a
    have h1: c^2-a*c+a^2 ≤ a^2 := by nlinarith
    -- rewriting into goal it suffices to show a^2b^2(a^2-ab+b^2) ≤ 12
    suffices a^2*b^2*(a^2-a*b+b^2) ≤ 12 by
      calc (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2)
      _ ≤ (a ^ 2 - a * b + b ^ 2) * (b ^ 2) * (a ^ 2) := by apply mul_le_mul ; apply mul_le_mul; norm_num; assumption; nlinarith; nlinarith; linarith; nlinarith; apply mul_nonneg; nlinarith; nlinarith;
      _ ≤ 12 := by linarith
    -- let a+b=p and ab=q
    let q:(∃ p:ℝ, p = a+b) := by
      use a+b
    obtain ⟨p, pdef⟩ := q
    let q':(∃ q:ℝ, q = a*b) := by
      use a*b
    obtain ⟨q, qdef⟩ := q'
    -- obvious that p<3
    have p3: p ≤ 3 := by linarith
    -- q ≤ 9/4 by amgm
    have q94: q ≤ 9/4 := by
      rw [qdef];
      have hamgm: a * b ≤ ((a+b)/2)^2 := by nlinarith
      calc a * b
      _ ≤ ((a+b)/2)^2 := by assumption
      _ = (p/2)^2 := by rw [pdef]
      _ ≤ 9/4 := by nlinarith
    -- we now rewrite the goal with p and q
    conv_lhs =>
      calc a ^ 2 * b ^ 2 * (a ^ 2 - a * b + b ^ 2)
      _ = q^2 * (p^2-3*q) := by rw [qdef, pdef]; ring_nf
    have h2:q ^ 2 * (p ^ 2 - 3 * q) ≤ q^2 * (9 - 3 * q) := by apply mul_le_mul_of_nonneg_left; nlinarith; nlinarith
    apply le_trans h2
    suffices 0 ≤ 4 - q ^ 2 * (3 - q) by linarith
    -- now it's a simple factoring
    conv_rhs =>
      calc 4 - q ^ 2 * (3 - q)
      _ = 4 - 3*q^2 + q^3 := by ring_nf
      _ = (q-2)^2*(q+1) := by ring_nf
    apply mul_nonneg; nlinarith; nlinarith
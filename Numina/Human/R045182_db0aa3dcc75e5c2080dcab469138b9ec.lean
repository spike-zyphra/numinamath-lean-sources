import Mathlib

/- 10. Given the sequence $\left\{a_{n}\right\}$, where $a_{1}=2$, and the sum of the first $n$ terms is $S_{n}$. If $\left(n^{2}+1\right) \cdot a_{n+1}=(2 n+1) \cdot S_{n}+n^{4}$ $+2 n^{3}+3 n^{2}+2 n+2$, find the expressions for $S_{n}$ and $a_{n}$ (expressed in the simplest form involving $n$). -/
theorem algebra_253423 {a : ℕ → ℝ} {S : ℕ → ℝ}
    (sdef : ∀ n, S n = ∑ i in Finset.Ico 1 (n+1), a i)
    (ha1 : a 1 = 2) (hsum : ∀ n, (n ^ 2 + 1) * a (n + 1) = (2 * n + 1) * S n + n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n + 2) :
    ∀ n≥1, a n = 3 * n ^ 2 - 3 * n + 2 ∧ S n = n * (n ^ 2 + 1) := by
    intro n
    -- we know that a (n+1) = S (n+1) - S n
    have h0:∀n, a (n+1) = S (n+1) - S n := by
      intro n
      induction n with
      | zero => simp [*]
      | succ n' ih =>
        conv_rhs =>
          calc _
          _ = ∑ k ∈ Finset.Ico 1 (n' + 2), a k + a (n' + 1 + 1) - ∑ i ∈ Finset.Ico 1 (n' + 1 + 1), a i := by rw [sdef, sdef, Finset.sum_Ico_succ_top (by omega)]
          _ = a (n' + 1 + 1) + (∑ k ∈ Finset.Ico 1 (n' + 2), a k - ∑ i ∈ Finset.Ico 1 (n' + 1 + 1), a i) := by ring_nf
          _ = a (n' + 1 + 1) := by ring_nf
    -- we can rewrite hsum with that
    conv at hsum =>
      intro n; rw [h0 n]
    -- simplifying gives a nice recursive relation
    have h1:∀n, (S (n+1))/((n+1)^2+1) - (S n)/(n^2+1)=1 := by
      intro n; specialize hsum n
      apply congr_arg (fun x => x - (2 * ↑n + 1) * S n ) at hsum
      conv_lhs at hsum =>
        calc _
        _ = (n ^ 2 + 1) * S (n + 1) - (n^2 + 2*n + 2) * S n := by ring_nf
        _ = (n ^ 2 + 1) * S (n + 1) - ((n+1)^2 + 1) * S n := by ring_nf
      apply congr_arg (fun x => x / ((n:ℝ)^2+1) / ((n+1)^2+1) ) at hsum
      conv_rhs at hsum =>
        calc _
        _ = ((n:ℝ) ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n + 2 ) / (n ^ 2 + 1) / ((n + 1) ^ 2 + 1) := by ring_nf
        _ = (n^2+1)*((n+1)^2+1) / (n ^ 2 + 1) / ((n + 1) ^ 2 + 1) := by ring_nf
        _ = 1 := by rw [mul_comm, mul_div_assoc, div_self (by nlinarith), mul_one, div_self (by nlinarith)];
      conv_lhs at hsum =>
        calc _
        _ = (↑n ^ 2 + 1) * S (n + 1) / (↑n ^ 2 + 1) / ((↑n + 1) ^ 2 + 1) - ((↑n + 1) ^ 2 + 1) * S n / (↑n ^ 2 + 1) / ((↑n + 1) ^ 2 + 1) := by ring_nf
        _ = ((↑n ^ 2 + 1)/ (↑n ^ 2 + 1)) * S (n + 1)  / ((↑n + 1) ^ 2 + 1) - (((↑n + 1) ^ 2 + 1) / ((↑n + 1) ^ 2 + 1)) * S n / (↑n ^ 2 + 1) := by ring_nf
        _ = S (n + 1)  / ((↑n + 1) ^ 2 + 1) - S n / (↑n ^ 2 + 1) := by rw [div_self (by nlinarith), div_self (by nlinarith), one_mul, one_mul]
      assumption
    -- therefore we can easily calculate S n/(n^2+1)
    have h2:∀n, S n/(n^2+1) = n := by
      intro n
      induction n with
      | zero => simp [*]
      | succ n' ih =>
        specialize h1 n'; rw [ih] at h1
        apply congr_arg (fun x => x + (n':ℝ)) at h1; rw [sub_add, sub_self, sub_zero] at h1
        norm_cast at h1 ⊢
        rw [h1]
        ring_nf
    -- so S n = n * (n^2+1)
    have h3:∀n, S n = n * (n^2+1) := by
      intro n
      specialize h2 n
      rw(config := { occs := .pos [1]}) [← h2]
      rw [div_mul, div_self (by nlinarith), div_one]
    -- now the conclusion is trivial
    intro hn
    constructor
    rotate_left
    exact h3 n
    suffices (a n:ℝ) = 3 * n ^ 2 - 3 * n + 2 by
      rw [this]
    let q:∃ m:ℕ, n=m+1 ∧ m = n-1 := by
      use n-1; omega
    obtain ⟨m, ⟨nm, mn⟩⟩ := q
    rw [nm, h0 m]
    suffices S (m + 1) + 3 * ↑(m + 1) = 3 * ↑(m + 1) ^ 2 + 2 + S m by linarith
    rw [h3, h3]
    norm_cast; ring_nf
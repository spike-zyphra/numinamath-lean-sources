import Mathlib

/- (9) (14 points) Given the sequence $\left\{a_{n}\right\}$ satisfies $\frac{a_{n+1}+a_{n}-1}{a_{n+1}-a_{n}+1}=n\left(n \in \mathbf{N}^{*}\right)$, and $a_{2}=6$.
(1) Find the general term formula of the sequence $\left\{a_{n}\right\}$;
(2) Let $b_{n}=\frac{a_{n}}{n+c}\left(n \in \mathbf{N}^{*}\right)$, where $c$ is a non-zero constant. If the sequence $\left\{b_{n}\right\}$ is an arithmetic sequence, let $c_{n}=\frac{b_{n}}{2^{n}}$, and $S_{n}=c_{1}+c_{2}+\cdots+c_{n}$, find $S_{n}$. -/
variable {a : ℕ → ℤ}

theorem algebra_215906_1 (ha : ∀ n, (a (n + 1) + a n - 1) = (n + 1) * (a (n + 1) - a n + 1))
    (ha1 : a 1 = 6) : ∀ n, a n = (n + 1) * (2 * n + 1) := by
  have ha' : ∀ n, n * a (n + 1) - (n + 2) * a n = -(n + 2)
  · intro n
    linarith [ha n]
  intro n
  -- Do small cases first
  by_cases hn : n < 1
  · rw [Nat.lt_one_iff] at hn
    rw [hn]
    have := ha' 0
    simp at this
    rw [this]
    norm_num
  push_neg at hn
  -- Conclude by a simple induction on n
  induction' n, hn using Nat.le_induction with n' hn' ih
  · simp [ha1]
  · have h1 := ha' n'
    rw [ih] at h1
    have h2 : n' * a (n' + 1) = n' * ((n' + 1 + 1) * (2 * (n' + 1) + 1))
    · linarith
    rw [Nat.cast_add, Nat.cast_one]
    exact mul_left_cancel₀ (by linarith) h2


theorem algebra_215906_2 {c : ℚ}
  (hpos : c > 0)
  (ha : ∀ n, a n = (n + 1) * (2 * n + 1)) :
  let b := fun (n : ℕ) => (a n / (n + 1 + c) : ℚ);
  (∀ n, b n = b 0 + n * (b 1 - b 0)) →
  ∀ n, ∑ i ∈ Finset.range (n + 1), b i / 2^i = 8 - 2 * (n + 3) / (2^n : ℚ) := by
  intro b hb
  -- Find the value of c, this follows easily from b an arithmetic sequence
  have hc : c = -1/2
  · have hb1 := hb 2
    simp [b, ha] at hb1
    field_simp at hb1
    nlinarith
  -- Show b n = 2 * (n + 1)
  have hb' : ∀ n, b n = 2 * (n + 1)
  · intro n
    have h1 : (2 * n + 1 : ℚ) = 2 * (n + 1 - 1/2)
    · linarith
    simp [b, hc, ha]
    rw [h1, mul_div_assoc, show (n : ℚ) + 1 + -1/2 = (n : ℚ) + 1 - 1/2 by ring, mul_div_cancel_right₀, mul_comm]
    linarith
  -- Rewrite in the sum
  have h_sum : ∀ n, b n / 2 ^ n = 2 * (n + 1) / 2^n
  · intro i; rw [hb']
  intro n
  rw [Finset.sum_congr rfl (fun i hi => h_sum i)]
  -- Conclude with an easy induction
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih]; field_simp; ring
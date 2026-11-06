import Mathlib

/- 11. (15 points) The sequence $\left\{a_{n}\right\} n \geqslant 1$ is defined as $a_{1}=1$, $a_{2}=4, a_{n}=\sqrt{a_{n-1} a_{n+1}+1}(n \geqslant 2)$.
(1) Prove that the sequence $\left\{a_{n}\right\} n \geqslant 1$ is an integer sequence;
(2) Prove that $2 a_{n} a_{n+1}+1(n \geqslant 1)$ is a perfect square. -/
theorem algebra_276502 {a : ℕ → ℝ}
    (ha1 : a 0 = 1) (ha2 : a 1 = 4)
    (han : ∀ n, a (n + 1) = √ (a n * a (n + 2) + 1)) :
    (∀ n, ∃ m : ℤ, a n = m) ∧
    (∀ n, ∃ k : ℕ, k^2 = 2 * a n * a (n + 1) + 1) := by
  -- we have shifted index by -1, as that is easier to work with
  -- first we prove all a(n) are positive, for 0 this is easy, for m+1, use the recursion and positivity
  have h_a_pos (n : ℕ) : 0 < a n := by
    induction n with
    | zero => rw [ha1]; norm_num
    | succ m hm =>
      rw [han]
      simp
      rw [han]
      positivity
  -- using positivness of all a(n) and the recursive equation for n and n+1, square them and subtract to get following ratio
  have h_a_ratio (n : ℕ) : (a n + a (n + 2)) / (a (n + 1)) = (a (n + 1) + a (n + 3)) / (a (n + 2)) := by
    have := h_a_pos n
    have := h_a_pos (n + 1)
    have := h_a_pos (n + 2)
    have := h_a_pos (n + 3)
    field_simp
    have ha1 := congrArg (· ^ 2) (han n)
    simp at ha1
    rw [Real.sq_sqrt (by positivity)] at ha1
    have ha2 := congrArg (· ^ 2) (han (n+1))
    simp at ha2
    rw [Real.sq_sqrt (by positivity)] at ha2
    linarith
  -- commpute a(2) = 15
  have ha3 : a 2 = 15 := by
    have := h_a_pos 2
    have := han 0
    rw [ha1, ha2] at this
    have := congrArg (· ^ 2) this
    simp only at this
    rw [Real.sq_sqrt (by positivity)] at this
    linarith
  -- the ratio fact means the ratio is always (a(0) + a(2)) / a(1) which is 4
  replace h_a_ratio (n : ℕ) : (a n + a (n+2)) / a (n + 1) = 4 := by
    induction n with
    | zero => rw [ha1, ha2, ha3]; norm_num
    | succ m hm =>
      rw [← h_a_ratio, hm]
  -- this means we get a easier recursion form the ratio
  have han' (n : ℕ) : a (n + 2) = 4 * a (n + 1) - a n := by
    have := h_a_pos (n + 1)
    have := h_a_ratio n
    field_simp at this
    linarith
  -- now we prove first goal as a lemma to use it multiple times, the recursion easily allows us to prove it
  have ht₁ (n : ℕ) : ∃ (m : ℤ), a n = m := by
    induction n using Nat.twoStepInduction with
    | zero => rw [ha1]; use 1; norm_cast
    | one => rw [ha2]; use 4; norm_cast
    | more m hm1 hm2 =>
      obtain ⟨m₁, hm₁⟩ := hm1
      obtain ⟨m₂, hm₂⟩ := hm2
      rw [han', hm₁, hm₂]
      use 4 * m₂ - m₁
      norm_cast
  and_intros
  -- first goal is just the lemma
  . exact ht₁
  -- for second goal, we can prove 0 = a(k+2) * (a(k+2) - 4*a(k+1) + a(k)) = (a(k+2) - a(k+1))^2 - (2*a(k+2)*a(k+1) + 1)
  . rintro n
    match n with
    | 0 =>
      rw [ha1, ha2]
      use 3
      norm_num
    | k + 1 =>
      have h_eq := calc
        0 = a (k + 2) * (a (k + 2) - 4 * a (k + 1) + a k) := by rw [han']; ring
        _ = a (k + 2)^2 - 4 * a (k + 1) * a (k + 2) + a k * a (k + 2) := by ring
        _ = a (k + 2)^2 - 4 * a (k + 1) * a (k + 2) + (a (k + 1)^2 - 1) := by
          congr
          have := h_a_pos k
          have := h_a_pos (k + 2)
          have := congrArg (· ^ 2) (han k)
          simp only at this
          rw [Real.sq_sqrt (by positivity)] at this
          linarith
        _ = (a (k + 2) - a (k + 1))^2 - (2 * a (k + 2) * a (k + 1) + 1) := by ring
      -- by using ht₁ to extract integers m₁, m₂, we can use |m₁ - m₂| as witness
      obtain ⟨m₁, hm₁⟩ := ht₁ (k + 1)
      obtain ⟨m₂, hm₂⟩ := ht₁ (k + 2)
      use (m₁ - m₂).natAbs
      have : ((m₁ - m₂).natAbs ^ 2 : ℝ) = ↑(((m₁ - m₂).natAbs : ℤ) ^ 2) := by norm_cast
      rw [this, Int.natAbs_sq]
      push_cast
      rw [← hm₁, ← hm₂]
      linarith
import Mathlib


/-A sequence consists of $2010$ terms.  Each term after the first is 1 larger than the previous term.  The sum of the $2010$ terms is $5307$.  When every second term is added up, starting with the first term and ending with the second last term, what is the sum?
-/
theorem algebra_12473 {a : ℕ → ℤ} {x₁ : ℤ} (ha : a 0 = x₁)
    (h : ∀ i, a (i + 1) = a i + 1) (hsum : ∑ i < 2010, a i = 5307) :
    ∑ i < 1005, a (2 * i) = 2151 := by
  -- We label the terms $x_1, x_2, x_3, \ldots, x_{2009},x_{2010}$.
  -- Suppose that $S$ is the sum of the odd-numbered terms in the sequence; that is, \[ S = x_1 + x_3 + x_5 + \cdots + x_{2007}+x_{2009} \]
  -- a 0 = x₁, a 1 = x₂, a 2 = x₃, ...
  have : ∃S, ∑ i < 1005, a (2 * i) = S := by simp
  rcases this with ⟨S, hS⟩
  rw [hS]
  -- Next, we pair up the terms: each odd-numbered term with the following even-numbered term. That is, we pair the first term with the second, the third term with the fourth, and so on, until we pair the 2009th term with the 2010th term. There are 1005 such pairs.
  -- In each pair, the even-numbered term is one bigger than the odd-numbered term. That is, $x_2-x_1=1$, $x_4-x_3=1$, and so on.  Therefore, the sum of the even-numbered terms is 1005 greater than the sum of the odd-numbered terms.
  have : (fun x ↦ a (2 * x + 1) - a (2 * x)) = fun x ↦ 1 := by
    ext x
    have h := h (2 * x)
    simp at h
    rw [h]
    linarith

  -- Thus, the sum of the even-numbered terms is $S+1005$.
  have : ∑ i < 1005, a (2 * i + 1) = S + 1005 := by
    rw [hS.symm]
    have : ∑ i < 1005,  a (2 * i + 1) - ∑ i < 1005, a (2 * i) = 1005 := by
      rw [Finset.sum_sub_distrib.symm, Finset.sum, this]
      rw [←Finset.sum, Finset.sum_const]
      simp
    linarith
  -- Since the sum of all of the terms equals the sum of the odd-numbered terms plus the sum of the even-numbered terms, then $S+(S+1005)=5307$ or $2S=4302$ or $S=2151$.  Thus, the required sum is $\boxed{3156}$.
  have : 5307 = S + (S + 1005) := by
    have hp (n : ℕ) (f: ℕ → ℤ) :
      (∑ i ∈ Finset.Iio (2 * n), f i) = (∑ i ∈ Finset.Iio n, f (2 * i)) + (∑ i ∈ Finset.Iio n, f (2 * i + 1)) := by
        induction' n with n ih
        · simp
          rw [show Finset.Iio 0 = ∅ by rfl]
          simp
        · have (p : ℕ): Finset.Iio p = Finset.range p := by
            ext n
            simp
          rw [this, this, show 2 * (n + 1) = 2 * n + 1 + 1 by linarith]
          rw [this, this] at ih
          rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          linarith
    rw [hsum.symm, this.symm, hS.symm, hp 1005 a]
  linarith

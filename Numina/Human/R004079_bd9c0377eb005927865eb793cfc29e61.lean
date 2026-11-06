import Mathlib

/- 10.4. The sequence of integers $a_{n}$ is defined as follows: $a_{n+1}=a_{n}^{2}-a_{n}+1, a_{1}=100$. Prove that any two distinct terms of the sequence are coprime. -/
theorem number_theory_236446 (a : ℕ → ℤ)
    (h₁ : ∀ n, a (n + 1) = a n ^ 2 - a n + 1) :
    ∀ m n, m ≠ n → IsCoprime (a m) (a n) := by
  intro m n hmn
  -- Without loss of generality, assume that m < n.
  wlog hlt : m < n generalizing m n
  · symm
    apply this n m hmn.symm
    omega
  -- We have n = m + (n - m).
  rw [show n = m + (n - m) by omega]
  have hk0 : n - m ≠ 0 := by omega
  -- Let k = n - m ≠ 0.
  generalize n - m = k at hk0 ⊢
  -- It is enough to show that a (m + k) = c * a m + 1 for some c ∈ ℤ.
  suffices ∃ c, a (m + k) = c * a m + 1 by
    have ⟨c, hc⟩ := this
    simp [hc, IsCoprime]
    -- We have -c * a m + 1 * a (m + k) = -c * a m + c * a m + 1 = 1,
    -- so a(m) and a(m + k) are coprime.
    use -c, 1
    ring
  clear hmn hlt n
  -- Show that a (m + k) = c * a m + 1 by induction.
  let rec h : (k : ℕ) → (hk : k ≠ 0) → ∃ c, a (m + k) = c * a m + 1
  -- If k = 0, then 0 ≠ 0 is a contradiction.
  | 0 => by simp
  -- If k = 1 then a (m + 1) = a n * (a n - 1) + 1.
  | 1 => by
    simp [h₁]
    use a m - 1
    ring
  | k + 2 => by
    simp
    -- Consider k + 2 and find c such that
    -- a (m + (k + 1)) = c * a m + 1.
    have ⟨c, hc⟩ := h (k + 1) (by simp)
    rw [show m + (k + 2) = m + (k + 1) + 1 by ring, h₁, hc]
    -- Show that a (m + (k + 2)) = (c ^ 2 * a m + 2 * c - c) * a m + 1.
    use c ^ 2 * a m + 2 * c - c
    ring
  exact h k hk0
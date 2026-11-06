import Mathlib

/-Given a sequence of numbers $F_{1}, F_{2}, \ldots ; F_{1}=F_{2}=1$ and $F_{n+2}=F_{n}+F_{n+1}$. Prove that $F_{5 k}$ is divisible by 5 for $k=1,2, \ldots$.-/
theorem number_theory_200613 {F : ℕ → ℕ} (hF : ∀ n, F (n + 2) = F n + F (n + 1))
    (hF1 : F 1 = 1) (hF2 : F 2 = 1) (k : ℕ) :
    5 ∣ F (5 * k) := by
  -- We will use induction on k.
  -- First, we verify the base case when k = 0.
  have hF0 : F 0 = 0 := by
    have eq1 := hF 0
    have eq2 := hF 1
    simp at eq1 eq2
    linarith [hF1, eq1, eq2]

  induction k with
  | zero =>
    have h1 : F (5 * 0) = F 0 := by simp
    rw [h1]
    exact ⟨0, by simp [hF0]⟩
  | succ k ih =>
    -- Now assume that the statement holds for k, i.e., 5 divides F(5*k).
    have h1 : F (5 * (k + 1)) = F (5 * k + 5) := by ring_nf
    rw [h1]
    have h2 : F (5 * k + 5) = F (5 * k + 3) + F (5 * k + 4) := by
      apply hF
    have h3 : F (5 * k + 4) = F (5 * k + 2) + F (5 * k + 3) := by
      apply hF
    have h4 : F (5 * k + 3) = F (5 * k + 1) + F (5 * k + 2) := by
      apply hF
    have h5 : F (5 * k + 2) = F (5 * k) + F (5 * k + 1) := by
      apply hF
    rw [h2, h3, h4, h5]
    omega
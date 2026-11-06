import Mathlib

/- We define a recursive sequence $S'$ that is equivalent to $S$ -/
def S' : ℕ → ℤ
| 0 => 0
| n + 1 => let sn := S' n
           let ans := if sn < n + 1 then 1 else -1
           let sns := sn + (n + 1) * ans
           sns

/- We prove that the maximum value of $k \leq 2010$ such that $S' k = 0$ is $1092$ -/
lemma lemma_1 : IsGreatest {k ≤ 2010 | S' k = 0} 1092 := by
  constructor
  . -- Calculate $S' 1092$
    native_decide
  . -- Rewrite the goal as a decidable proposition
    intro x ⟨hx₁, hx₂⟩
    contrapose! hx₂
    have hx : x ∈ Finset.Ioc 1092 2010 := Finset.mem_Ioc.mpr ⟨hx₂, hx₁⟩
    clear hx₁ hx₂
    revert x
    -- Compute by brute force
    native_decide

/- Let $S_{0}=0$ and let $S_{k}$ equal $a_{1}+2 a_{2}+\ldots+k a_{k}$ for $k \geq 1$. Define $a_{i}$ to be 1 if $S_{i-1}<i$ and -1 if $S_{i-1} \geq i$. What is the largest $k \leq 2010$ such that $S_{k}=0$ ? -/
theorem algebra_608625 (a S : ℕ → ℤ) (hS₀ : S 0 = 0) (hS : ∀ k ≥ 1, S k = ∑ i ∈ Finset.Icc 1 k, i * a i) (ha : ∀ i ≥ 1, a i = if S (i - 1) < i then 1 else -1) :
    IsGreatest {k ≤ 2010 | S k = 0} 1092 := by

  -- We prove that $S_{k+1} = S k + (k + 1) * a_{k+1}$ by simple induction
  have H₀ (k : ℕ) : S (k + 1) = S k + (k + 1) * a (k + 1) := by
    induction k with
    | zero => simp [hS, hS₀]
    | succ k ih => simp [hS (k + 1) (Nat.succ_pos k), hS (k + 1 + 1) (Nat.succ_pos (k + 1)), Finset.sum_Icc_succ_top (Nat.succ_pos (k + 1))]

  -- We prove that $S k = S' k$ by simple induction
  have H₁ (k : ℕ) : S k = S' k := by
    induction k with
    | zero => simp [hS₀, S']
    | succ k ih => simpa [H₀, S', ih, -mul_ite, show (k + 1 : ℤ) ≠ 0 by positivity] using ha (k + 1)

  -- We are done using the previous lemmas
  simpa [H₁] using lemma_1

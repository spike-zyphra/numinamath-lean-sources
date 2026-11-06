import Mathlib

theorem number_theory_3420 {N : ℕ} (hN : N > 1000) :
    (N / 1000) ^ 3 = N ↔ N = 32768 := by
  constructor
  · -- Assume (N / 1000) ^ 3 = N, prove N = 32768
    intro h
    have h1 : N > 1000 := hN
    have h2 : (N / 1000) ^ 3 = N := h
    have h3 : N = (N / 1000) ^ 3 := by
      linarith
    have h4 : N % 1000 < 1000 := by
      omega
    have h5 : N = (N / 1000) * 1000 + N % 1000 := by
      omega
    -- Now we need to show $N = 32768$.
    -- Let's solve.
    -- Let $M = N / 1000$.
    -- So $M^3 = (N / 1000) \cdot 1000 + N \mod 1000$.
    -- Rearranged: $M^3 - M \cdot 1000 = N \mod 1000$.
    -- So $0 \leq M^3 - M \cdot 1000 < 1000$.
    -- So $0 \leq M^3 - 1000 \cdot M < 1000$.
    -- So $M \geq 32$: since $31^3 < 1000 \cdot 31$. $31^3 = 29791 < 31000$.
    -- And $M \leq 32$: because for $M = 33$, $33^3 - 1000 \cdot 33 > 1000$.
    -- So $32$ is the only possible value.
    -- Check $M = 32$: $32^3 = 32768$
    -- Check $32768 / 1000 = 32$: yes.
    -- Check $(32) ^ 3 = 32768$: yes.
    -- So it is a solution. Since our analysis shows it's the only solution, we need to prove $N = 32768$ in Lean 4.
    have eq1 : (N / 1000 : ℕ) ^ 3 = (N / 1000 : ℕ) * 1000 + N % 1000 := by
      nlinarith [h4, h5, h2]
    have h7 : (N / 1000 : ℕ) ≤ 215 := by
      by_contra h8
      push_neg at h8
      have h12 : (N / 1000 : ℕ) ≥ 216 := by
        omega
      have h10 : N < (N / 1000 + 1 : ℕ) * 1000 := by
        have h11 : N % 1000 < 1000 := by
          omega
        have h12 : N = (N / 1000 : ℕ) * 1000 + N % 1000 := by
          omega
        nlinarith
      nlinarith [sq_nonneg (N % 1000 : ℕ), sq_nonneg ((N / 1000 : ℕ) : ℕ), sq_nonneg ((N / 1000 : ℕ) ^ 2 : ℕ)]
    interval_cases h8 : (N / 1000 : ℕ) <;> try { 
      omega 
    } 
  · -- Assume N = 32768, prove (N / 1000) ^ 3 = N
    intro h
    rw [h]
    norm_num
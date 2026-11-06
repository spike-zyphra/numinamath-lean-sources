import Mathlib
open Matrix
noncomputable section

-- Define the Fibonacci sequence.
def F : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

/-It can be shown that for any positive integer $n,$
\[\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}^n = \begin{pmatrix} F_{n + 1} & F_n \\ F_n & F_{n - 1} \end{pmatrix},\]where $F_n$ denotes the $n$th Fibonacci number.
Compute $F_{784} F_{786} - F_{785}^2.$-/
theorem calculus_7245 {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A = !![1, 1; 1, 0]) :
    F 784 * F 786 - F 785 ^ 2 = -1 := by
  -- Determinant power rule: $det(A^n) = det(A)^n$.
  have h_det_pow : ∀ n : ℕ, det (A ^ n) = det A ^ n := by
    intro n
    exact det_pow A n

  -- Compute $det(A) = -1$.
  have h_det_A : det A = -1 := by
    rw [hA]
    simp [det_fin_two]

  -- Combine to get $det(A^n) = (-1)^n$.
  have h_det_A_n : ∀ n : ℕ, det (A ^ n) = (-1) ^ n := by
    intro n
    rw [h_det_pow, h_det_A]

  -- Prove $det(A^n) = F (n + 1) * F (n - 1) - F n ^ 2$.
  have h_det_fib : ∀ n : ℕ, n ≥ 1 → det (A ^ n) = F (n + 1) * F (n - 1) - F n ^ 2 := by
    intro n hn
    have h_fib_matrix : A ^ n = !![F (n + 1), F n; F n, F (n - 1)] := by
      induction' n with k hk
      · simp at hn
      · cases' k with m
        · simp [hA, F]
        · have h_succ : A ^ (m + 2) = A * (A ^ (m + 1)) := by
            rw [pow_succ']
          rw [h_succ, hk (by linarith)]
          simp [hA, mul_apply, dotProduct, F]
    rw [h_fib_matrix]
    simp [det_fin_two]
    ring

  -- Derive $F (n + 1) * F (n - 1) - F n ^ 2 = (-1)^n$.
  have h_fib_identity : ∀ n : ℕ, n ≥ 1 → F (n + 1) * F (n - 1) - F n ^ 2 = (-1) ^ n := by
    intro n hn
    rw [← h_det_A_n, h_det_fib n hn]

  -- Set $n = 785$, verify $F 784 * F 786 - F 785 ^ 2 = -1$.
  have h_final : F 784 * F 786 - F 785 ^ 2 = -1 := by
    have h_785 : 785 ≥ 1 := by linarith
    have h_fib_785 : F (785 + 1) * F (785 - 1) - F 785 ^ 2 = (-1) ^ 785 := by
      exact h_fib_identity 785 h_785
    have h_neg_one : (-1 : ℤ) ^ 785 = -1 := by
      apply Odd.neg_one_pow
      decide
    rw [h_neg_one] at h_fib_785
    linarith

  exact h_final

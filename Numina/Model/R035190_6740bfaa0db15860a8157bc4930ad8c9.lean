import Mathlib

theorem algebra_148594 (n : ℕ) :
  ∑ i in Finset.range n, (-1 : ℤ)^i * (i+1)^2 = (-1 : ℤ)^(n-1) * (n * (n+1)) / 2 := by
  cases n with
  | zero =>
    simp
  | succ n =>
    induction n with
    | zero =>
      simp
      <;> norm_num
      <;> ring_nf
      <;> tauto
      <;> try { omega }
      <;> simp [show (-1 : ℤ) ^ (0: ℕ) = (1: ℤ) by simp]
      <;> simp [Int.add_assoc, add_assoc, pow_zero, mul_zero, zero_add]
    | succ n ih =>
      have eq1 : ∑ i in Finset.range (n + 1 + 1), (-1 : ℤ)^i * (i + 1)^2 =
        ∑ i in Finset.range (n + 1), (-1 : ℤ)^i * (i + 1)^2 + (-1 : ℤ)^(n + 1) * (n + 2)^2 := by
        rw [Finset.sum_range_succ]
        all_goals norm_num
        <;> try { ring_nf <;> simp }
      rw [eq1]
      rw [ih]
      -- Simplify the right-hand side using the induction hypothesis
      simp [pow_zero, pow_succ, Int.add_mul, Int.mul_add, mul_assoc, add_mul, mul_add]
      <;> ring_nf
      <;> try { 
        simp [Nat.pow_succ, Int.add_mul, mul_add, mul_assoc, add_mul, mul_add, pow_succ, Nat.succ_eq_add_one, mul_add, add_mul]
        <;> norm_num 
        <;> try omega 
      }
      <;> try { 
        omega
        <;> tauto
        <;> try { induction n }
        <;> try { ring_nf <;> omega }
        <;> try { 
          simp [Nat.pow_succ, pow_succ]
          <;> ring_nf 
          <;> norm_num 
          <;> try { tauto } 
          <;> try { 
            ring_nf 
            <;> try { 
              tauto <;> try { 
                induction n
              }
            }
          }
          <;> try { 
            ring_nf 
            <;> try { 
              omega
            }
          }
        }
      }
      <;> try { 
        induction n 
        <;> try { 
          simp [Nat.pow_succ, pow_succ]
          <;> ring_nf 
          <;> try { tauto } 
          <;> try { 
            ring_nf 
            <;> try { 
              tauto 
              <;> try { 
                induction n
                <;> try { 
                  simp [Nat.pow_succ, pow_succ]
                  <;> ring_nf 
                  <;> try { tauto }
                  <;> try { induction n }
                }
              }
            }
          }
          <;> try { 
            ring_nf 
            <;> try { 
              tauto <;> try { 
                induction n <;> try { simp [Nat.pow_succ, pow_succ] }
              }
            }
          }
        }
      }
      <;> try { 
        ring_nf 
        <;> try { 
          assumption
          <;> tauto 
          <;> try { 
            native_decide
          }
        }
        <;> try { 
          native_decide
        }
        <;> try { 
          native_decide
        }
      }
      <;> try { 
        native_decide 
      }
      <;> try { 
        tauto 
        <;> try { native_decide }
        <;> try { 
          native_decide
        }
      }
      <;> try { 
        native_decide 
      }
      all_goals try { 
        tauto 
        <;> try { native_decide } 
      }
      all_goals try { 
        native_decide 
      }
      all_goals try { 
        nlinarith [sq_nonneg ((-1 : ℤ)), sq_nonneg (n ^ 2), sq_nonneg ((n + 1) ^ 2), sq_nonneg ((n + 2 : ℤ) ^ 2)]
      }
      all_goals try { 
        induction n <;> try { simp [Nat.pow_succ, pow_succ] }
      }
      all_goals try { 
        nlinarith [sq_nonneg ((-1 : ℤ)), sq_nonneg (n ^ 2), sq_nonneg ((n + 1) ^ 2), sq_nonneg ((n + 2) ^ 2)]
      }
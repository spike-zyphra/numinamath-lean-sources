import Mathlib

open Finset BigOperators

/-An infinite sequence of real numbers a 1,a 2,… satisfies the recurrence: ∀ n:ℕ , a (n+3) = a (n+2) - 2 * a (n+1) + a n,
Given that a 1 = a 3 = 1, a 98 = a 99, compute a 1 + a 2 + ... a 100.
-/
theorem Algebra_609499  (a : ℕ → ℝ ) (ha : ∀ n, a (n+3) = a (n+2) - 2 * a (n+1) + a n)
  (ha1 : a 1 = 1) (ha3 : a 3 = 1) (ha98 : a 98 = a 99): ∑ i in range 100 , a (i+1) = 3:=by{
    -- First, we proof that forall n ≥ 3, ∑ i in range n, a (i+1) = 2 * a 1 + a 3 - a (n-2) + a (n-1).
    have key (n : ℕ) (hn : n ≥ 3): ∑ i in range n, a (i+1) = 2 * a 1 + a 3 - a (n-2) + a (n-1):=by{
      -- simplify the left side step-by-step.
      -- extract the first three numbers.
      calc ∑ i in range n, a (i+1) = ∑ i in range (n-3+3), a (i+1) :=by field_simp
        _ = a 1 + a 2 + a 3 + ∑ i in range (n-3), a (i+4) :=by{
          rw [Finset.sum_range_succ']
          rw [Finset.sum_range_succ']
          rw [Finset.sum_range_succ']
          simp
          ring
        }
        _ = a 1 + a 2 + a 3 + ∑ i in range (n-3), (a (i+3) - 2 * a (i+2) + a (i+1)):=by{
          have h1: ∑ i in range (n-3), a (i+4) = ∑ i in range (n-3), (a (i+3) - 2 * a (i+2) + a (i+1)):=by{
            exact sum_congr rfl fun x a => ha (x + 1)
          }
          rw [h1]
        }
        _ = a 1 + a 2 + a 3 + ∑ i in range (n-3), (a (i+3) - a (i+2) - (a (i+2) - a (i+1))) :=by{
          have h2 : ∑ i in range (n-3), (a (i+3) - 2 * a (i+2) + a (i+1)) = ∑ i in range (n-3), (a (i+3) - a (i+2) - (a (i+2) - a (i+1))) :=by{
            apply sum_congr rfl
            intro x hx
            ring
          }
          rw [h2]
        }
        _ = a 1 + a 2 + a 3 + ∑ i in range (n-3), (a (i+3) - a (i+2)) - ∑ i in range (n-3), (a (i+2) - a (i+1)) :=by{
          rw [ Finset.sum_sub_distrib]
          ring
        }
        -- use Finset.sum_range_sub to simplify.
        _ = 2 * a 1 + a 3 - a (n-2) + a (n-1) :=by{
          rw [Finset.sum_range_sub (λ i ↦ a (i+2))]
          rw [Finset.sum_range_sub (λ i ↦ a (i+1))]
          calc a 1 + a 2 + a 3 + (a (n - 3 + 2) - a (0 + 2)) - (a (n - 3 + 1) - a (0 + 1)) = a 1 + a 2 + a 3 + a (n - 1) - a 2 - (a (n - 2) - a 1) :=by {
              have h3 : n - 3 + 2 = n - 1:=by{
                refine Eq.symm (Nat.eq_add_of_sub_eq ?hle rfl)
                exact Nat.le_sub_one_of_lt hn
              }
              have h4: n - 3 + 1 = n - 2 :=by{
                refine Eq.symm ((fun {b a c} h => (Nat.sub_eq_iff_eq_add h).mp) ?h rfl)
                exact Nat.le_sub_of_add_le hn
              }
              rw [h3, h4]
              ring
            }
            _ = 2 * a 1 + a 3 - a (n-2) + a (n-1):=by ring
        }
    }
    -- now n=100, use key.
    rw [key 100]
    simp
    rw [ha1, ha3, ha98]
    simp
    ring
    exact Nat.le_of_ble_eq_true rfl
}

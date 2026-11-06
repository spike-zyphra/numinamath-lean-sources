import Mathlib

open Nat Finset

theorem number_theory_608227 (n : ℕ) (hn : n > 0) : n.divisors.sum φ = n := by
  -- Rewrite as ∑ d ∣ n, φ(n / d)
  rw [← Nat.sum_div_divisors n φ]
  -- Show that n = ∑ d ∣ n, #{k ∈ range n | n.gcd k = d}
  have : n = ∑ d ∈ n.divisors, #{k ∈ range n | n.gcd k = d} := by
    nth_rw 1 [← card_range n]
    -- The function "fun k ↦ n.gcd k" partitions the range of [0, n) with labels in n.divisors
    -- So the size of the range is the sum of the sizes of the fibers
    refine card_eq_sum_card_fiberwise fun x _ => mem_divisors.2 ⟨?_, hn.ne'⟩
    apply Nat.gcd_dvd_left
  nth_rw 3 [this]
  -- #{k ∈ range n | n.gcd k = d} = φ(n / d)
  exact sum_congr rfl fun x hx => totient_div_of_dvd (dvd_of_mem_divisors hx)

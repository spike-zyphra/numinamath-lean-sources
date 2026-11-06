import Mathlib

/- One of Euler's conjectures was disproved in the 1960s by three American mathematicians when they showed there was a positive integer such that
$133^{5}+110^{5}+84^{5}+27^{5}=n^{5}$.
Find the value of $n$.-/

theorem number_theory_95556 : ∃ n : ℕ, 0 < n ∧ 133^5 + 110^5 + 84^5 + 27^5 = n^5 := by
--to prove existence, we exhibit one such $n$, then we show it satisfies the two conditions.
  use 144
  exact ⟨by linarith, by norm_num⟩
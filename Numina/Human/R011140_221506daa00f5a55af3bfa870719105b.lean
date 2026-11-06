import Mathlib
open Mathlib
/-- Call a positive integer $n$ extra-distinct if the remainders when $n$ is divided by $2, 3, 4, 5,$ and $6$ are distinct. Find the number of extra-distinct positive integers less than $1000$. -/
theorem number_theory_98649 :
Set.ncard {n | n < 1000 ∧ n % 2 ≠ n % 3 ∧ n % 2 ≠ n % 4 ∧ n % 2 ≠ n % 5 ∧ n % 2 ≠ n % 6 ∧ n % 3 ≠ n % 4 ∧ n % 3 ≠ n % 5 ∧ n % 3 ≠ n % 6 ∧ n % 4 ≠ n % 5 ∧ n % 4 ≠ n % 6 ∧ n % 5 ≠ n % 6} = 49 := by
  have inter : {n | n < 1000 ∧ n % 2 ≠ n % 3 ∧ n % 2 ≠ n % 4 ∧ n % 2 ≠ n % 5 ∧ n % 2 ≠ n % 6 ∧ n % 3 ≠ n % 4 ∧ n % 3 ≠ n % 5 ∧ n % 3 ≠ n % 6 ∧ n % 4 ≠ n % 5 ∧ n % 4 ≠ n % 6 ∧ n % 5 ≠ n % 6} = {35, 58, 59, 95, 118, 119, 155, 178, 179, 215, 238, 239, 275, 298, 299, 335, 358, 359, 395, 418, 419, 455, 478, 479, 515, 538, 539, 575, 598, 599, 635, 658, 659, 695, 718, 719, 755, 778, 779, 815, 838, 839, 875, 898, 899, 935, 958, 959, 995} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases s1 : Even n
      -- Case 1: $n \equiv 0 \pmod{2}$
      · have sub1 : n % 2 = 0 := by clear * - s1; exact Nat.even_iff.mp s1
        -- Then, $n \equiv 2 \pmod{4}$, which implies $n \equiv 1 \pmod{3}$ and $n \equiv 4 \pmod{6}$, and therefore $n \equiv 3 \pmod{5}$. Using CRT, we obtain $n \equiv 58 \pmod{60}$
        have sub2 : n % 60 = 58 := by omega
        -- 16 cases in total
        (obtain o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o : n = 58 ∨ n = 118 ∨ n = 178 ∨ n = 238 ∨ n = 298 ∨ n = 358 ∨ n = 418 ∨ n = 478 ∨ n = 538 ∨ n = 598 ∨ n = 658 ∨ n = 718 ∨ n = 778 ∨ n = 838 ∨ n = 898 ∨ n = 958 := by omega) <;> subst n <;> decide
      -- Case 2: $n \equiv 1 \pmod{2}$
      · have sub1 : n % 2 = 1 := by clear * - s1; exact Nat.not_even_iff.mp s1
        -- $n$ is then $3 \pmod{4}$. If $n \equiv 0 \pmod{3}$, $n \equiv 3 \pmod{6}$, a contradiction. Thus, $n \equiv 2 \pmod{3}$, which implies $n \equiv 5 \pmod{6}$. $n$ can either be $0 \pmod{5}$, which implies that $n \equiv 35 \pmod{60}$ by CRT, giving $17$ cases; or $4 \pmod{5}$, which implies that $n \equiv 59 \pmod{60}$ by CRT, giving $16$ cases.
        obtain sub2 | sub2 : n % 60 = 35 ∨ n % 60 = 59 := by omega
        -- 17 cases in total
        · (obtain o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o : n = 35 ∨ n = 95 ∨ n = 155 ∨ n = 215 ∨ n = 275 ∨ n = 335 ∨ n = 395 ∨ n = 455 ∨ n = 515 ∨ n = 575 ∨ n = 635 ∨ n = 695 ∨ n = 755 ∨ n = 815 ∨ n = 875 ∨ n = 935 ∨ n = 995 := by omega) <;> subst n <;> decide
        -- 16 cases in total
        · (obtain o | o | o | o | o | o | o | o | o | o | o | o | o | o | o | o : n = 59 ∨ n = 119 ∨ n = 179 ∨ n = 239 ∨ n = 299 ∨ n = 359 ∨ n = 419 ∨ n = 479 ∨ n = 539 ∨ n = 599 ∨ n = 659 ∨ n = 719 ∨ n = 779 ∨ n = 839 ∨ n = 899 ∨ n = 959 := by omega) <;> subst n <;> decide
    -- all listed integers satisfy the conditions
    · intro h
      (obtain ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga | ga := h) <;> subst n <;> decide
  simp_rw [inter]
  (repeat rw [Set.ncard_insert_of_not_mem]) <;> try decide
  rw [Set.ncard_singleton]
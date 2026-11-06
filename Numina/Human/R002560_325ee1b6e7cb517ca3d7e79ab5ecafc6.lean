import Mathlib
open Mathlib
/-- Ms. Math's kindergarten class has $16$ registered students. The classroom has a very large number, $N$, of play blocks which satisfies the conditions:

(a) If $16$, $15$, or $14$ students are present in the class, then in each case all the blocks can be distributed in equal numbers to each student, and

(b) There are three integers $0 < x < y < z < 14$ such that when $x$, $y$, or $z$ students are present and the blocks are distributed in equal numbers to each student, there are exactly three blocks left over.

Find the sum of the distinct prime divisors of the least possible value of $N$ satisfying the above conditions. -/

theorem number_theory_95434 n (h : IsLeast { N : ℕ | (16 ∣ N ∧ 15 ∣ N ∧ 14 ∣ N) ∧ (∃ (x y z : ℕ), 0 < x ∧ x < y ∧ y < z ∧ z < 14 ∧ (N % x = 3) ∧ (N % y = 3) ∧ (N % z = 3)) } n) : n.primeFactors.sum id = 148 := by
  have ytw : IsLeast { N : ℕ | (16 ∣ N ∧ 15 ∣ N ∧ 14 ∣ N) ∧ (∃ (x y z : ℕ), 0 < x ∧ x < y ∧ y < z ∧ z < 14 ∧ (N % x = 3) ∧ (N % y = 3) ∧ (N % z = 3)) } 220080 := by
    constructor
    -- The witnesses we can choose are \(x = 9\), \(y = 11\), and \(z = 13\).
    · norm_num
      exists 9; norm_num
      exists 11; norm_num
      exists 13
    · simp_rw [mem_lowerBounds, Set.mem_setOf]
      intros x hx
      obtain ⟨⟨h1, h2, h3⟩, x1, y, z, h4, h5, h6, h7, h8, h9, h10⟩ := hx
      -- $N$ must be some multiple of $\text{lcm}(14, 15, 16)= 2^{4}\cdot 3\cdot 5\cdot 7$ ; this $lcm$ is hereby denoted $k$ and $N = qk$.
      obtain ⟨q, t1⟩ : 1680 ∣ x := by omega
      -- x1 = 9, y = 11, z = 13. We prove that this is the only possible tuple by checking all values from 1 to 13 for each variable.
      -- This can be done individually for each variable. Therefore, there is no combinatorial explosion.
      have wu : z = 9 ∨ z = 11 ∨ z = 13 := by
        (obtain it | it | it | it | it | it | it | it | it | it | it | it | it : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 ∨ z = 10 ∨ z = 11 ∨ z = 12 ∨ z = 13 := by omega) <;> subst z <;> omega
      have ww : x1 = 9 ∨ x1 = 11 ∨ x1 = 13 := by
        (obtain it | it | it | it | it | it | it | it | it | it | it | it | it : x1 = 1 ∨ x1 = 2 ∨ x1 = 3 ∨ x1 = 4 ∨ x1 = 5 ∨ x1 = 6 ∨ x1 = 7 ∨ x1 = 8 ∨ x1 = 9 ∨ x1 = 10 ∨ x1 = 11 ∨ x1 = 12 ∨ x1 = 13 := by omega) <;> subst x1 <;> omega
      have wt : y = 9 ∨ y = 11 ∨ y = 13 := by
        (obtain it | it | it | it | it | it | it | it | it | it | it | it | it : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 ∨ y = 10 ∨ y = 11 ∨ y = 12 ∨ y = 13 := by omega) <;> subst y <;> omega
      -- Now, because of h4, h5, and h6, we can conclude x1 = 9, y = 11, z = 13.
      have sta1 : x1 = 9 := by omega
      have sta2 : y = 11 := by omega
      have sta3 : z = 13 := by omega
      clear wu ww wt
      subst x1 y z
      norm_num at *
      cases x with
      | zero => norm_num at *
      | succ x =>
        cases x with
        | zero => norm_num at *
        | succ x =>
          cases x with
          | zero => norm_num at *
          | succ x =>
            norm_num at *
            have ga1 : 9 ∣ x := by clear * - h8; omega
            have ga2 : 11 ∣ x := by clear * - h9; omega
            have ga3 : 13 ∣ x := by clear * - h10; omega
            -- x is divisible by 1287
            have yy : 1287 ∣ x := by clear * - ga1 ga2 ga3; omega
            -- now we conclude the goal
            clear * - t1 yy; omega
  have wld : n = 220080 := by
    obtain ⟨ytw, tw⟩ := ytw
    obtain ⟨h, g⟩ := h
    rw [mem_lowerBounds] at tw g
    have := tw _ h
    have b := g _ ytw
    exact Nat.le_antisymm (g 220080 ytw) (tw n h)
  subst n
  native_decide
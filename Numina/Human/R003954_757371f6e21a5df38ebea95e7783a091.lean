import Mathlib

/- 8.41. One hundred positive numbers $x_{1}, x_{2}, \ldots, x_{100}$ satisfy the conditions


$$

\begin{aligned}
& x_{1}^{2}+x_{2}^{2}+\ldots+x_{100}^{2}>10000 \\
& x_{1}+x_{2}+\ldots+x_{100}<300
\end{aligned}

$$


Prove that among them, there are three numbers whose sum is greater than 100.

See also problem 18.4.

## 8.8. Convexity -/
theorem inequalities_224831 (x : Fin 100 → ℝ)
    (hx : ∀ i, 0 < x i)
    (hsum : ∑ i, x i ^ 2 > 10000)
    (hsum' : ∑ i, x i < 300) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x i + x j + x k > 100 := by

      -- wlog, x is monotone
      wlog hm : Monotone x
      -- else we sort the values of x
      -- they will still be positive
      · have sort_pos : ∀ (i : Fin 100), 0 < (x ∘ ⇑(Tuple.sort x)) i
          := fun i => hx ((Tuple.sort x) i)

        -- the sum of their squares will still be greater than 10000
        have sort_sum_sq : ∑ i : Fin 100, (x ∘ (Tuple.sort x)) i ^ 2 > 10000 := by
          simp only [Function.comp_apply, Equiv.sum_comp (Tuple.sort x) (fun i => x i ^ 2)]
          exact hsum

        -- the sum will still be less than 300
        have sort_sum : ∑ i : Fin 100, (x ∘ (Tuple.sort x)) i < 300 := by
          simp only [Function.comp_apply, Equiv.sum_comp (Tuple.sort x)]
          exact hsum'

        -- then we have three x values with a sum greater than 100
        obtain ⟨i, j, k, ij, jk, ki, hh⟩ := this (x ∘ (Tuple.sort x)) sort_pos sort_sum_sq sort_sum (Tuple.monotone_sort x)

        -- but these x values are also part of the unsorted x values
        exists (Tuple.sort x) i
        exists (Tuple.sort x) j
        exists (Tuple.sort x) k

        -- simplify
        norm_num at hh ⊢

        -- we're done
        tauto

      -- so assume x is sorted

      -- if any three x values are gonna have a sum greater than 100, it's gonna be the largest ones: x_99, x_98 and x_97
      exists 99, 98, 97
      split_ands
      -- we chose different values
      · omega
      · omega
      · omega
      -- note that x_98 and x_97 are non-negative
      · have pos_1 : 0 < x 98 := hx 98
        have pos_2 : 0 < x 97 := hx 97

        -- consider when x_99 is at least 100
        by_cases max_gt : 100 ≤ x 99
        -- then the sum is clearly greater than 100
        · linarith

        -- so assume that x_99 < 100
        norm_num at max_gt

        -- note that x_98 is at most x_99
        have le_2 : x 98 ≤ x 99 := by
          apply hm
          omega

        -- note that x_97 is at most x_98
        have le_3 : x 97 ≤ x 98 := by
          apply hm
          omega

        -- then we have that 100 * (x 97 + x 98 + x 99) > 10000
        have bound_three : 100 * (x 97 + x 98 + x 99) > 10000 := by
          -- we chain inequalities
          calc
            -- subtract (100 - x_99) * (x_99 - x_97) and (100 - x_98) * (x_98 - x_97)
            _ ≥ 100 * (x 97 + x 98 + x 99) - (100 - x 99) * (x 99 - x 97) - (100 - x 98) * (x 98 - x 97) := by
              have pos_3 : 0 ≤ (x 99 - x 97) := by linarith
              have pos_4 : 0 ≤ (x 98 - x 97) := by linarith
              have pos_5 : 0 ≤ (100 - x 98) := by linarith
              nlinarith
            -- which is equal to x_97 * (300 - x_99 - x_98) + x_98 ^ 2 + x_99 ^ 2
            _ = x 97 * (300 - x 99 - x 98) + x 98 ^ 2 + x 99 ^ 2 := by ring
            -- but we know that the sum is less than 300, so we have a lower bound of
            -- x_97 * (∑ x - x_99 - x_98) + x_98 ^ 2 + x_99 ^ 2
            _ > x 97 * (∑ i : Fin 100, x i - x 99 - x 98) + x 98 ^ 2 + x 99 ^ 2 := by gcongr
            -- which is equal to
            -- x_97 * (x_0 + .. + x_97) + x_98 ^ 2 + x_99 ^ 2
            _ = x 97 * (∑ i : Fin 98, x i.castSucc.castSucc) + x 98 ^ 2 + x 99 ^ 2 := by
              congr
              -- extract terms
              iterate 2 rw [Fin.sum_univ_castSucc]

              -- simplify
              have last_99 : (Fin.last 99) = 99 := by rfl
              have last_98 : (Fin.last 98).castSucc = 98 := by rfl
              rw [last_99, last_98]
              ring
            -- distribute multiplication over sum
            _ = (∑ i : Fin 98, x 97 * x i.castSucc.castSucc) + x 98 ^ 2 + x 99 ^ 2 := by
              congr
              apply Finset.mul_sum
            -- but (x_97 * x_0 + ... x_97 * x_97) ≥ (x_0 * x_0 + ... x_97 * x_97)
            _ ≥ (∑ i : Fin 98, x i.castSucc.castSucc ^ 2) + x 98 ^ 2 + x 99 ^ 2 := by
              -- compare terms
              gcongr with i hi
              · rw [pow_two]
                gcongr
                · exact le_of_lt <| hx i.castSucc.castSucc
                · apply hm
                  cases' i with i ih
                  norm_num
                  exact Fin.succ_le_succ_iff.mp ih
            -- merge terms into sum
            _ = ∑ i : Fin 100, x i ^ 2 := by
              -- extract two terms from the sum
              rw [Fin.sum_univ_castSucc (fun i => x i ^ 2)]
              rw [Fin.sum_univ_castSucc (fun i => x i.castSucc ^ 2)]
              -- then both sides are termwise equal
              congr
            -- and we already have a bound on ∑ (x_i ^ 2), so we're done
            _ > 10000 := hsum

        -- so then x_97 + x_98 + x_99 is larger than 100
        linarith
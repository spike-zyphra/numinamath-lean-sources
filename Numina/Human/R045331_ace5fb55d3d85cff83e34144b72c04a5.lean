import Mathlib

/-- Three bags of jelly beans contain 26, 28, and 30 beans. The ratios of yellow beans to all beans
in each of these bags are $50\%$, $25\%$, and $20\%$, respectively. All three bags of candy are
dumped into one bowl. Which of the following is closest to the ratio of yellow jelly beans to all
beans in the bowl?

$\text{(A)}\ 31\% \qquad \text{(B)}\ 32\% \qquad \text{(C)}\ 33\% \qquad \text{(D)}\ 35\% \qquad
\text{(E)}\ 95\%$ -/
theorem algebra_93550 (b1 b1' b2 b2' b3 b3' : ℕ)
    (h1 : b1 + b1' = 26) (h2 : b2 + b2' = 28) (h3 : b3 + b3' = 30)
    (h1' : 2 * b1 = b1 + b1') (h2' : 4 * b2 = b2 + b2') (h3' : 5 * b3 = b3 + b3') :
  42 * (b1 + b2 + b3) = 13 * (b1 + b1' + b2 + b2' + b3 + b3') := by

  -- Let $b_i$ be the number of yellow balls in the $i$-th bag and $b_i'$ be the number of non-yellow
  -- balls in the $i$-th bag, so the total number of balls in the $i$-th bag is $b_i + b_i'$.

  -- In the first bag, there are $26$ balls, so $b_1 + b_1' = 26$. 50\% of them are yellow, so
  -- $2 b_1 = b_1 + b_1'$. Therefore, $b_1 = 13$ and $b_1' = 13$.
  have hb1 : b1 = 13 := by
    calc _ = 2 * b1 / 2 := by omega
         _ = (b1 + b1') / 2 := by rw [h1']
         _ = 26 / 2 := by rw [h1]
         _ = _ := by norm_num
  have hb1' : b1' = 13 := by
    calc _ = b1 + b1' - b1 := by omega
         _ = 26 - b1 := by rw [h1]
         _ = 26 - 13 := by rw [hb1]
         _ = _ := by norm_num

  -- In the second bag, there are $28$ balls, so $b_2 + b_2' = 28$. 25\% of them are yellow, so
  -- $4 b_2 = b_2 + b_2'$. Therefore, $b_2 = 7$ and $b_2' = 21$.
  have hb2 : b2 = 7 := by
    calc _ = 4 * b2 / 4 := by omega
         _ = (b2 + b2') / 4 := by rw [h2']
         _ = 28 / 4 := by rw [h2]
         _ = _ := by norm_num
  have hb2' : b2' = 21 := by
    calc _ = b2 + b2' - b2 := by omega
         _ = 28 - b2 := by rw [h2]
         _ = 28 - 7 := by rw [hb2]
         _ = _ := by norm_num

  -- In the third bag, there are $30$ balls, so $b_3 + b_3' = 30$. 20\% of them are yellow, so
  -- $5 b_3 = b_3 + b_3'$. Therefore, $b_3 = 6$ and $b_3' = 24$.
  have hb3 : b3 = 6 := by
    calc _ = 5 * b3 / 5 := by omega
         _ = (b3 + b3') / 5 := by rw [h3']
         _ = 30 / 5 := by rw [h3]
         _ = _ := by norm_num
  have hb3' : b3' = 24 := by
    calc _ = b3 + b3' - b3 := by omega
         _ = 30 - b3 := by rw [h3]
         _ = 30 - 6 := by rw [hb3]
         _ = _ := by norm_num

  -- In all there are $13 + 7 + 6 = 26$ yellow balls and $13 + 21 + 24 = 58$ non-yellow balls.
  have yellow : b1 + b2 + b3 = 26 := by rw [hb1, hb2, hb3]
  have nonyellow : b1' + b2' + b3' = 58 := by rw [hb1', hb2', hb3']
  -- So there are $26 + 58 = 84$ balls in total.
  have total : b1 + b1' + b2 + b2' + b3 + b3' = 84 := by rw [hb1, hb1', hb2, hb2', hb3, hb3']

  -- Thus, the ratio of yellow balls to total balls is $26 / 84 = 13 / 42$.
  rw [yellow, total]
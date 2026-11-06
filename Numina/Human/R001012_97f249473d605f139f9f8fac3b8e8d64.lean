import Mathlib


/-A certain organism begins as two cells. Each cell splits and becomes two cells at the end of three days. At the end of another three days, every cell of the organism splits and becomes two cells. This process lasts for a total of 15 days, and no cells die during this time. How many cells are there at the end of the $15^\text{th}$ day?-/
theorem algebra_19845 (n : ℕ) (hn : n = 15) :
    2*2^(n/3) = 64 := by
    --根据题目可知生长周期为3天，第一个周期为细菌的数量为2，
    -- 可以得到公式2*2^(n/3)
    -- 当n=15时，处于第六个周期 代入公式得到2*2^(15/3)=64
    rw[hn]
    simp

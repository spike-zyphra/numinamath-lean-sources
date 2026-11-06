import Mathlib

/- A new green technology can be installed in your home for a one-time installation cost of $\$10,\!000$ and annual maintenance costs of $\$650$ per year. If the green technology is supposed to save you $\$1200$ each year in energy bills, how many whole years will it take to recuperate your costs? -/
theorem algebra_21750 (cost : ℝ) (annual_cost : ℝ) (savings : ℝ)
    (hcost : cost = 10000) (hanual_cost : annual_cost = 650) (hsavings : savings = 1200) :
    ⌈cost / (savings - annual_cost)⌉ = 19 := by
        -- 代入已知数值
        rw [hcost, hanual_cost, hsavings]

        -- 证明向上取整值大于18
        have h1 : ⌈(200 : ℝ) / 11⌉ > 18:= by
            have h : 18 < ⌈(200 : ℝ) / 11⌉ ↔ ↑18 < (200 : ℝ) / 11:= Int.lt_ceil
            exact h.2 (by linarith)

        -- 证明向上取整值小于等于19
        have h2 : ⌈(200 : ℝ) / 11⌉ ≤ 19:= by
            have h : ⌈(200 : ℝ) / 11⌉ ≤ 19 ↔ (200 : ℝ) / 11 ≤ ↑19:= Int.ceil_le
            exact h.2 (by linarith)
        norm_num  -- 使用norm_num策略完成证明

import Mathlib

/- Karla drove her vehicle 12,000 miles last year. How many gallons of gasoline would she have saved last year had she driven a fuel-efficient hybrid car averaging 48 miles per gallon rather than an SUV averaging 15 miles per gallon? -/
theorem algebra_21331 (d : ℝ) (h : d = 12000) (v1 v2 : ℝ) (h1 : v1 = 48) (h2 : v2 = 15) :
    d / v2 - d / v1 = 550 := by
    -- 第一步：将d替换为12000
    calc _ = 12000 / v2 - 12000 / v1:= by rw [h]
         -- 第二步：将v1替换为48，v2替换为15
         _ = 12000 / 15 - 12000 / 48:= by rw[h1,h2]
         -- 第三步：计算 12000/15 = 800 和 12000/48 = 250
         _ = 800 - 250:= by ring_nf
         -- 第四步：计算最终结果 800 - 250 = 550
         _ = 550:= by ring_nf

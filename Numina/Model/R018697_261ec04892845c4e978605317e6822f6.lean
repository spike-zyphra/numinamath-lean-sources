import Mathlib

/- 3. Let's determine the share of the Japanese yen in the currency structure of the NWF funds as of 01.12.2022 using one of the following methods:

First method:

a) Find the total amount of NWF funds allocated to Japanese yen as of 01.12.2022:

$J P Y_{22}=1388.01-41.89-2.77-309.72-554.91-0.24=478.48$ (billion rubles)

b) Determine the share of the Japanese yen in the currency structure of the NWF funds as of 01.12.2022:

$\alpha_{22}^{J P Y}=\frac{478.48}{1388.01} \approx 34.47(\%)$

c) Calculate by how many percentage points and in which direction the share of the Japanese yen in the currency structure of the NWF funds changed over the period considered in the table:

$\Delta \alpha^{J P Y}=\alpha_{22}^{J P Y}-\alpha_{21}^{J P Y}=34.47-47.06=-12.59 \approx-12.6$ (p. p.)

Second method:

a) Determine the share of the euro in the currency structure of the NWF funds as of 01.12.2022:

$\alpha_{22}^{E U R}=\frac{41.89}{1388.01} \approx 3.02(\%)$

b) Determine the share of the Japanese yen in the currency structure of the NWF funds as of 01.12.2022:

$\alpha_{22}^{J P Y}=100-3.02-0.2-22.31-39.98-0.02=34.47(\%)$

c) Calculate by how many percentage points and in which direction the share of the Japanese yen in the currency structure of the NWF funds changed over the period considered in the table:

$\Delta \alpha^{J P Y}=\alpha_{22}^{J P Y}-\alpha_{21}^{J P Y}=34.47-47.06=-12.59 \approx-12.6$ (p. p.) -/
theorem algebra_214081 {α : ℕ → ℝ} (hα : α 22 = 34.47 / 100) (hα' : α 21 = 47.06 / 100) :
    α 22 - α 21 = -12.59 / 100 := by
  rw [hα, hα']
  all_goals norm_num
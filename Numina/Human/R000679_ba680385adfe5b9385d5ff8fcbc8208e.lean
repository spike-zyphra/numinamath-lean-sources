import Mathlib

/- Determine the value of
\[\frac{\frac{2016}{1} + \frac{2015}{2} + \frac{2014}{3} + \dots + \frac{1}{2016}}{\frac{1}{2} + \frac{1}{3} + \frac{1}{4} + \dots + \frac{1}{2017}}.\] -/
theorem algebra_13902 : (∑ i ∈ Finset.range 2016, (2016 - i) / (i + 1 : ℚ)) / (∑ i ∈ Finset.range 2016, (1 : ℚ) / (i + 2)) = 2017 := by native_decide

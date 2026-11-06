import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/- 10. Length of the river (from 8th grade. 2 points).
The Anchurian Geographical Society (GSA) sent an expedition with the goal of measuring the length of the great Anchurian river Rio-Coralio.
It turned out that the length of the riverbed from the source to the mouth is 402 km plus or minus 500 m,
with a probability of error of 0.04, and errors in either direction are equally likely.

Independently from GSA, the AWRA (Anchurian Water Resources Agency) conducted its own study on this topic.
The result: 403 km plus or minus 500 m.
The probability of error is also 0.04, and, again, errors in either direction are equally likely.

When the results of the surveys were compared and it was confirmed that there were no errors in the methods or measurements,
the president of GSA and the director of AWRA jointly turned to the Absent-Minded Scientist,
who is a recognized expert in statistics, to explain the discrepancy.
The Scientist was delighted and said,
"Now I know the length of Rio-Coralio with a small probability of error."
How could he reason?
Find the estimate and the probability of error. -/
theorem other_272937
  {P : Measure ℝ} [IsProbabilityMeasure P]
  {l : ℝ}
  {p₁ p₂ : ℝ≥0∞}
  (hval : l = 402.5 ∧ p₁ = 2/100 ∧ p₂ = 2/100)
  (h₁ : P (Set.Iio l) = p₁)
  (h₂ : P (Set.Ioi l) = p₂) : 1 = P {l} + p₁ + p₂ := by
  -- we know P(L > 402.5) = 0.02 from GSA's survey
  -- we know P(L < 402.5) = 0.02 from AWRA's survey
  -- so P(L = 402.5) = 0.96
  have decomp : Set.univ = Set.Iio l ∪ {l} ∪ Set.Ioi l := by simp
  have : P Set.univ = P (Set.Iio l) + P {l} + P (Set.Ioi l) := by
    rw [decomp, measure_union (by simp) (by simp), measure_union (by simp) (by simp)]
  rw [measure_univ, h₁, h₂, add_comm p₁] at this
  exact this
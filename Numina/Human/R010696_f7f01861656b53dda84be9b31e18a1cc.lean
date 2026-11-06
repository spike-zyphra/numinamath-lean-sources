import Mathlib

/- In the $19^\text{th}$ century, Britain used a money system which included pence, farthings, shillings and pounds. The following conversions were used:

$\bullet$ $4 \text{ farthings} = 1 \text{ pence},$

$\bullet$ $12 \text{ pence} = 1 \text{ shilling},$

$\bullet$ $20 \text{ shillings} = 1 \text{ pound}.$

How many total farthings were equivalent to $1$ pound and $5$ pence? -/
theorem algebra_20040 (pence farthings shillings pounds : ℕ)
    (h₀ : 4 * farthings = 1 * pence) (h₁ : 12 * pence = 1 * shillings)
    (h₂ : 20 * shillings = 1 * pounds) :
    1 * pounds + 5 * pence = 980 * farthings := by
        omega

import Mathlib

def Heidi : ℝ := 2.1
def Lola : ℝ := 1.4

/- Heidi is $2.1 \mathrm{~m}$ tall, while Lola is $1.4 \mathrm{~m}$ tall. What is their average height?

A $1.525 \mathrm{~m}$
B $1.6 \mathrm{~m}$
C $1.7 \mathrm{~m}$
D $1.725 \mathrm{~m}$
E $1.75 \mathrm{~m}$-/
theorem arithmetic_4185 : (Heidi + Lola) / 2 = 1.75 := by
  -- verify by computation
  unfold Heidi Lola
  norm_num

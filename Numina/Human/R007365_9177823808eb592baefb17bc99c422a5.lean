import Mathlib

/- The letters of the alphabet are each assigned a random integer value, and $H=10$. The value of a word comes from the sum of its letters' values. If $MATH$ is 35 points, $TEAM$ is 42 points and $MEET$ is 38 points, what is the value of $A$? -/
theorem algebra_16241 (a b c d e f g h i j k l m n o p q r s t u v w x y z : ℤ)
    (h₀ : m + a + t + h = 35) (h₁ : t + e + a + m = 42) (h₂ : m + e + e + t = 38)
    (h₃ : h = 10) :
    a = 21 := by linarith

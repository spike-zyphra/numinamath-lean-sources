import Mathlib

/- A bug crawls along a number line, starting at −2. It crawls to −6, then turns around and crawls to 5. How many units does the bug crawl altogether?
(A) 9(B) 11(C) 13(D) 14(E) 15 -/
theorem algebra_93631 : |(-2 : ℤ) - (-6 : ℤ)| + |(-6 : ℤ) - 5| = 15 := by 
    --we solve the algebraic equation by means of linear algebra and absolute value properties
    simp
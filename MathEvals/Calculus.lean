import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Real.Basic

set_option linter.style.whitespace false

-- Evaluating that the derivative of a constant function is zero everywhere
theorem derivative_of_constant (c : ℝ) : deriv (fun _ : ℝ => c) = fun _ => 0 := by
  ext x
  exact deriv_const x c

-- Evaluating the linearity of the derivative operator for a scaled function
theorem derivative_scaling (f : ℝ → ℝ) (c : ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun x => c * f x) x = c * deriv f x := by
  exact deriv_const_mul c hf

-- Evaluating the derivative of a product of two differentiable functions
theorem derivative_product (f g : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun x => f x * g x) x = deriv f x * g x + f x * deriv g x := by
  exact deriv_mul hf hg

-- Evaluating a basic limit property or inequality over real intervals
lemma square_growth_bound (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) : x^2 ≤ 4 := by nlinarith

import Game.Levels.TermWorld.L01_HelloWorld

World "TermWorld"
Title "Term World"

Introduction "
The untyped lambda calculus is a small language that has two core concepts of
*abstraction* and *application*. As an example, we might have a term such:

$(λ x \\, . \\, λ y \\, . \\, x + y)$

that intuitively is a function that takes two arguments and adds them together.
In deciding how to represent this within a proof assistant, this presents some
challenges in deciding how to represent *variable binding* and *substitution*.

In this game we choose the *locally nameless* representation, which is in fact
what Lean itself uses.
"

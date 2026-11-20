import ConPastel.Translator.EvalM

/-!
# Identity tokens

CakeML has no pointer test, but it has references, and its `=` compares two
references by location. A datatype registered with `cake_token` stores, in
every constructor, a fresh reference allocated when the value is built
(`tokExp`, `ref ()`): its *identity token*. The invariant only says the token
is a reference (`TOKEN`), so the token carries no meaning — but two values
built separately have different tokens, and CakeML's `=` on two values
compares the tokens before the children.

So on such a type `=` is a *pointer test*: it returns at once (the stored
words, then the tokens, differ — or the two are the same object), and `true`
means equal values. It is no longer a decision of equality: equal values
built separately compare unequal.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- An identity token: some reference. -/
def TOKEN (v : Value) : Prop := ∃ n, v = .loc true n

/-- `ref ()`: a fresh identity token. -/
def tokExp : Exp := .app .opref [.con none []]

theorem Eval_tok (env : SemEnv Value) : Eval env tokExp TOKEN := by
  intro σ s
  have hu : Runs s env [.con none []] s (.val [.conv none []]) := ⟨0, 0, by simp [evaluate, doConCheck, buildConv]⟩
  have := Runs.opref hu
  exact ⟨_, [.refv (.conv none [])], this.evalRel, _, rfl⟩

end ConPastel.Translator

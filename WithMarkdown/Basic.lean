import ProofWidgets
import Lean
import Mathlib.Tactic

open ProofWidgets Lean ProofWidgets.Jsx

def showMarkdown (src : String) (stx : Syntax) : CoreM Unit := do
  let html : Html := <MarkdownDisplay contents={src}/>
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

initialize markdownEnvExt :
  SimplePersistentEnvExtension (UInt64 × String) (Std.HashMap UInt64 String) ←
  registerSimplePersistentEnvExtension {
    name := `markdownEnvExt
    addEntryFn := fun M (a,b) => M.insert a b
    addImportedFn := fun as => Id.run do
      let mut out := .empty
      for bs in as do
        for (x,y) in bs do
          out := out.insert x y
      return out
    toArrayFn := fun as => as.toArray
  }

syntax (name := withMarkdownTermStx) "md%" ident term : term
syntax (name := withMarkdownTacStx) "md%" ident tactic : tactic

@[term_elab withMarkdownTermStx]
def elabWithMarkdownTerm : Elab.Term.TermElab := fun stx type? =>
  match stx with
  | `(md% $id:ident $t:term) => do
    let id := id.getId
    let uid := hash id
    let env ← getEnv
    if let some markdown := markdownEnvExt.getState env |>.get? uid then
      showMarkdown markdown stx
    Elab.Term.elabTerm t type?
  | _ => Elab.throwUnsupportedSyntax

@[tactic withMarkdownTacStx]
def elabWithMarkdownTac : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic|md% $id:ident $t:tactic) => do
    let id := id.getId
    let uid := hash id
    let env ← getEnv
    if let some markdown := markdownEnvExt.getState env |>.get? uid then
      showMarkdown markdown stx
    Elab.Tactic.evalTactic t
  | _ => Elab.throwUnsupportedSyntax

elab "#add_md" id:ident s:str : command => do
  let id := id.getId
  let uid := hash id
  let markdown := s.getString
  modifyEnv fun env => markdownEnvExt.addEntry env (uid, markdown)

syntax (name := showMarkdownStx) "#md" ident : command

@[command_elab showMarkdownStx]
def elabShowMarkdown : Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(command|#md $id:ident) => do
    let id := id.getId
    let uid := hash id
    let env ← getEnv
    if let some markdown := markdownEnvExt.getState env |>.get? uid then
      Elab.Command.liftCoreM <| showMarkdown markdown stx
  | _ => Elab.throwUnsupportedSyntax

/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import DocGen4.Output.ToHtmlFormat
import DocGen4.Output.Navbar

namespace DocGen4
namespace Output

open scoped DocGen4.Jsx

/--
The HTML template used for all pages.
-/
def baseHtmlGenerator (title : String) (site : Array Html) : BaseHtmlM Html := do
  let moduleConstant :=
    if let some module := ← getCurrentName then
      #[<script>{s!"const MODULE_NAME={String.quote module.toString};"}</script>]
    else
      #[]
  pure
    <html lang="en">
      <body>
        [site]
        <nav class="nav">
          <iframe src={s!"{← getRoot}navbar.json"} class="navframe" frameBorder="0"></iframe>
        </nav>
      </body>
    </html>

/--
A comfortability wrapper around `baseHtmlGenerator`.
-/
def baseHtml (title : String) (site : Html) : BaseHtmlM Html := baseHtmlGenerator title #[site]

end Output
end DocGen4

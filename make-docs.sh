#!/bin/sh
# Build the Coqdoc HTML documentation for every theory in this
# development and collect it under docs/, with a landing page.
#
#   ./make-docs.sh          then open docs/index.html
#
# The per-theory pages are produced by dune's `@doc' alias, which
# runs rocqdoc over the .v sources.  Only comments written in the
# `(** ... *)' form appear in the output; plain `(* ... *)' comments
# are ignored by rocqdoc on purpose, and are used in this
# development for notes inside proof bodies.
set -e

cd "$(dirname "$0")"

echo "building documentation ..."
dune build @doc

rm -rf docs
mkdir -p docs

THEORIES="Algebra Utility Probability Crypto Compiler Examples"

for t in $THEORIES; do
  src="_build/default/$t/$t.html"
  if [ -d "$src" ]; then
    cp -R "$src" "docs/$t"
    chmod -R u+w "docs/$t"
    # rocqdoc's own stylesheet is kept as it comes: white background,
    # blue section headers.  An earlier version of this script replaced
    # it with a dark-mode one, which is not what is wanted here.
    # rocqdoc emits no viewport meta, so its pages render zoomed out on
    # a phone.  Add one to every generated page.
    for h in "docs/$t"/*.html; do
      [ -f "$h" ] || continue
      grep -q 'name="viewport"' "$h" || \
        sed -i '' 's|<head>|<head>\
<meta name="viewport" content="width=device-width, initial-scale=1" />|' "$h"
    done
    echo "  $t"
  else
    echo "  $t (no output, skipped)"
  fi
done

touch docs/.nojekyll

cat > docs/index.html <<'HTML'
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>SigmaLang — machine-checked documentation</title>
<style>
  /* Light, unconditionally: these pages sit next to rocqdoc's own
     output, which is white, and a landing page that followed the
     reader's system theme would not match it. */
  :root { color-scheme: light; }
  body { font: 16px/1.55 -apple-system, BlinkMacSystemFont, "Segoe UI",
         Roboto, Helvetica, Arial, sans-serif;
         max-width: 46rem; margin: 0 auto; padding: 2.5rem 1.25rem;
         background: #fff; color: #1a1a1a; }
  a { color: #0b5fa5; }
  h1 { font-size: 1.6rem; margin-bottom: .25rem; }
  p.sub { margin-top: 0; opacity: .75; }
  h2 { font-size: 1.1rem; margin-top: 2rem; }
  ul { list-style: none; padding-left: 0; }
  li { margin: .5rem 0; }
  a { text-decoration: none; }
  a:hover { text-decoration: underline; }
  .name { font-weight: 600; }
  .desc { opacity: .75; }
  p.sub, .desc { color: #444; opacity: 1; }
</style>
</head>
<body>
<h1>SigmaLang</h1>
<p class="sub">A compiler from a small statement language to sigma
protocols, with every security property machine-checked in Rocq.</p>

<h2>The compiler</h2>
<ul>
<li><a href="Compiler/toc.html"><span class="name">Compiler</span></a>
    <span class="desc">— the statement languages, the compiler, the
    composed protocol and its security proofs.</span></li>
<li><a href="Examples/toc.html"><span class="name">Examples</span></a>
    <span class="desc">— concrete instances over a real group: Helios
    ballots and decryption, CMZ credentials, Privacy Pass tokens, and
    the statement identifier.</span></li>
</ul>

<h2>Supporting libraries</h2>
<ul>
<li><a href="Crypto/toc.html"><span class="name">Crypto</span></a>
    <span class="desc">— the single-equation Schnorr protocol.</span></li>
<li><a href="Algebra/toc.html"><span class="name">Algebra</span></a>
    <span class="desc">— groups, rings, fields and vector spaces.</span></li>
<li><a href="Probability/toc.html"><span class="name">Probability</span></a>
    <span class="desc">— finite distributions, used to state zero
    knowledge.</span></li>
<li><a href="Utility/toc.html"><span class="name">Utility</span></a>
    <span class="desc">— vectors, a concrete prime-order group, SHA-256,
    string encodings, and a search space with a proof that its
    enumeration misses nothing.</span></li>
</ul>

<h2>Where to start</h2>
<ul>
<li><a href="Compiler/Compiler.LinearRelation.html"><span class="name">LinearRelation</span></a>
    <span class="desc">— the leaf protocol everything is built
    from.</span></li>
<li><a href="Compiler/Compiler.Composition.html"><span class="name">Composition</span></a>
    <span class="desc">— how leaves combine with AND, OR and
    thresholds.</span></li>
<li><a href="Compiler/Compiler.Surface.html"><span class="name">Surface</span></a>
    <span class="desc">— the language a user actually writes.</span></li>
<li><a href="Compiler/Compiler.DslNecessity.html"><span class="name">DslNecessity</span></a>
    <span class="desc">— why the well-formedness checker cannot be
    dropped.</span></li>
<li><a href="Compiler/Compiler.LeafValidity.html"><span class="name">LeafValidity</span></a>
    <span class="desc">— two more side conditions, and what goes wrong
    without them.</span></li>
</ul>
</body>
</html>
HTML

echo "documentation written to docs/index.html"

# undo decisions questionnaire

A 40-question browser-local questionnaire for the Nickel design discussion, requested by Ren. It asks what undo/redo should do in concrete histories. It has no answer key, grading or CRDT simulation; filling it out does not adopt a policy or verify an algorithm.

Live: **https://nickel-undo.shit.yachts/**

## use it

Choose an outcome or “another outcome” / “depends / unsure”, add optional explanations, and review or export at any point. There are no preselected choices. Question 40 is free text. Unanswered questions and draft notes survive export; a selected “unsure” counts as a response, not as a correct answer.

The JSON export contains the questionnaire revision, assumptions, every question and option, selected IDs and labels, notes and an optional respondent name. You can send that file yourself. Import accepts an unchanged same-version question snapshot and validates every answer before replacing the current response. It does not execute imported text. Import size is bounded at 8 MiB; individual notes are bounded at 10,000 UTF-16 code units.

Progress is saved in localStorage under a revision-scoped key. It is not uploaded. If storage is denied/full, the open tab still allows export and shows a warning. Another tab changing the saved response disables automatic overwrites from this stale tab; its in-memory response can still be exported. Explicit import/clear can replace the shared saved response. Private browsing or browser cleanup can erase local storage, so keep a file backup.

The app has no API, form submission or telemetry. Its CSP disallows network connections from scripts. Hosting still receives ordinary asset requests; this does not promise anonymous access or control over the public edge. The questionnaire is separately hosted so the main lynn-site writing site remains free of authored browser JavaScript.

## answer without a browser

Download [the Markdown questions](https://nickel-undo.shit.yachts/undo-questions.md) and [the blank response JSON](https://nickel-undo.shit.yachts/undo-answers-template.json). Both are generated from the unchanged web edition. Set respondent, then each answer.choiceId and answer.note; leave question snapshots intact. Choice IDs are strings ("1", "other", "unsure"), not numbers. Question 40 uses only its note. The web importer accepts this file and regenerates derived labels/status/counts on export. Send the completed JSON for comparison; no answers are chosen for you.

Run `node scripts/portable.mjs` after an intentional edition update. The locked check rejects stale generated files and checks blank/full response import roundtrips.

## run and check

This directory owns a locked flake independent of the Rust/hax proof environment.

```sh
nix flake check -L
nix build --no-link
nix run .                 # 127.0.0.1:4186; override with PORT
# against that running instance, in another shell:
nix develop .#browser --command node test/browser.mjs http://127.0.0.1:4186
```

`checks.default` checks the 40-question dataset, partial/full export and import rejection, and parses the app. Browser checks exercise actual downloaded JSON, reload persistence, import/clear, unsafe-text rendering, denied storage, stale-tab overwrite protection and 320/390/1280 widths. They use the locked Playwright/Chromium packages. Chromium mobile-sized viewports are not physical-phone/Safari acceptance.

The runtime package contains only `public/`; tests and docs are outside its startup build. There is no install step, external JS, font download or runtime dependency resolver.

## hosting

The repo-owned `units/nickel-undo-quiz.service` runs this worktree's flake app at loopback4186. This deployment uses `/root/projects/nickel-undo-quiz/questionnaire`.

```sh
rc-service add ./units/nickel-undo-quiz.service
rc-publish add nickel-undo 4186
```

After checked asset changes, restart only `nickel-undo-quiz.service`. No bridge service restart is involved. It is a static site with local response files, not part of Nickel's library runtime or Carbon's plugin architecture.

## implementation findings retained

The first browser launch used the wrong Playwright module path; the pinned package exposes `index.mjs` at its root. A live HTTP check also found darkhttpd serving `.mjs` as octet-stream; assets now use `.js` with a local module-type manifest. The browser subsequently loaded and exercised the actual modules. A Nix dynamic-attribute duplication was repaired before the final flake check. No failure is counted as a passing browser or build result.

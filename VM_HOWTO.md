# How to update code on the VM

You don't need Stergios to push files for you. Here's how.

---

## First time setup (run this once)

After you SSH in, run these lines. They install missing packages and load the API keys:

```bash
pip install python-dotenv openai
source ~/.env
```

If you get `ModuleNotFoundError: No module named 'dotenv'` or `No module named 'openai'`, run the pip line again.

If you get `AZURE_API_KEY` or `AZURE_OPENAI_ENDPOINT` errors, run `source ~/.env`. If that doesn't fix it, check the file exists:

```bash
cat ~/.env
```

You should see lines like `export AZURE_API_KEY=...`. If the file is missing, ask Stergios.

**Pro tip:** Add this to your `.bashrc` so it loads automatically every login:

```bash
echo 'source ~/.env' >> ~/.bashrc
```

After that you never have to think about it again.

---

## Edit files directly on the VM

SSH in and use `nano` (simplest editor):

```bash
ssh student1@20.86.154.197
nano ~/nestor/phase2_fol/fol_pipeline.py
```

- Arrow keys to move
- Edit text normally
- `Ctrl+O` then `Enter` to save
- `Ctrl+X` to exit

For quick one-line fixes, use `sed`:

```bash
sed -i 's/old text/new text/' ~/nestor/phase2_fol/fol_pipeline.py
```

---

## Upload files from your laptop

```bash
scp myfile.py student1@20.86.154.197:~/nestor/phase2_fol/
```

Upload a whole folder:

```bash
scp -r myfolder/ student1@20.86.154.197:~/nestor/
```

---

## Share files between students

Student homes are private. To share a file with everyone, put it in `/tmp/nestor_shared/`:

```bash
mkdir -p /tmp/nestor_shared
cp ~/nestor/phase2_fol/fol_pipeline.py /tmp/nestor_shared/
```

Other students can then:

```bash
cp /tmp/nestor_shared/fol_pipeline.py ~/nestor/phase2_fol/
```

Note: `/tmp` gets cleared on VM reboot. For permanent sharing, each student copies to their own home.

---

## Install Python packages

```bash
pip install packagename
```

This installs to your home folder (`~/.local`). Other students won't see it — each student installs their own.

---

## Check what's installed

```bash
pip list | grep packagename
which prover9
coqc --version
```

---

## Don't break things

- Don't edit `~/.env` keys — the API key is shared and costs money
- Don't delete other students' files
- Save experiments in your own home: `~/my_experiments/`
- If you break your nestor folder, ask Stergios to re-scp it

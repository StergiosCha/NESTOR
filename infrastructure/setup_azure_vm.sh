#!/bin/bash
# ============================================================
# NESTOR Azure VM Setup
# Run this ONCE on a fresh Ubuntu 22.04 VM to install everything.
#
# Usage:
#   ssh azureuser@YOUR_VM_IP
#   curl -O https://raw.githubusercontent.com/StergiosCha/NESTOR/master/infrastructure/setup_azure_vm.sh
#   chmod +x setup_azure_vm.sh
#   ./setup_azure_vm.sh
#
# After this, every student SSHs in and runs:
#   cd /opt/nestor
#   python3 demo.py
# ============================================================

set -e

echo "============================================"
echo "  NESTOR VM Setup — installing everything"
echo "============================================"

# ── System packages ──────────────────────────────────────
echo ""
echo "[1/6] Installing system packages..."
sudo apt-get update -qq
sudo apt-get install -y -qq \
    build-essential git python3 python3-pip python3-venv \
    opam ocaml wget curl unzip jq

# ── Prover9 + MACE4 (LADR) ──────────────────────────────
echo ""
echo "[2/6] Building Prover9 + MACE4 from source..."
cd /tmp
if [ ! -d "ladr" ]; then
    git clone https://github.com/laitep/ladr.git
fi
cd ladr
make all 2>&1 | tail -5
sudo cp bin/prover9 bin/mace4 /usr/local/bin/
echo "  ✓ prover9 installed: $(which prover9)"
echo "  ✓ mace4 installed: $(which mace4)"

# ── E Prover ─────────────────────────────────────────────
echo ""
echo "[3/6] Building E Prover..."
cd /tmp
if [ ! -d "eprover" ]; then
    git clone https://github.com/eprover/eprover.git
fi
cd eprover
./configure --prefix=/usr/local 2>&1 | tail -3
make 2>&1 | tail -5
sudo cp PROVER/eprover /usr/local/bin/
echo "  ✓ eprover installed: $(which eprover)"

# ── Coq ──────────────────────────────────────────────────
echo ""
echo "[4/6] Installing Coq via opam..."
opam init --auto-setup --disable-sandboxing --yes 2>&1 | tail -5
eval $(opam env)
opam install coq.8.20.1 --yes 2>&1 | tail -5
echo "  ✓ coqc installed: $(coqc --version 2>&1 | head -1)"

# Make coqc available system-wide
COQC_PATH=$(which coqc)
sudo ln -sf "$COQC_PATH" /usr/local/bin/coqc 2>/dev/null || true

# ── Python packages ──────────────────────────────────────
echo ""
echo "[5/6] Installing Python packages..."
pip3 install openai jupyter --break-system-packages -q
echo "  ✓ Python packages installed"

# ── Clone/setup NESTOR repo ──────────────────────────────
echo ""
echo "[6/6] Setting up NESTOR workspace..."
sudo mkdir -p /opt/nestor
sudo chown $USER:$USER /opt/nestor

# Copy skill if available, otherwise create workspace
if [ -d "$HOME/NESTOR" ]; then
    cp -r $HOME/NESTOR/* /opt/nestor/
elif [ -d "/opt/nestor/skill_nli-fol-prover" ]; then
    echo "  Workspace already exists"
else
    echo "  Creating workspace structure..."
    mkdir -p /opt/nestor/skill_nli-fol-prover/scripts
    mkdir -p /opt/nestor/skill_nli-fol-prover/examples
    mkdir -p /opt/nestor/data
    mkdir -p /opt/nestor/results
fi

# Download FraCaS if not present
if [ ! -f "/opt/nestor/data/fracas.xml" ]; then
    echo "  Downloading FraCaS XML..."
    wget -q -O /opt/nestor/data/fracas.xml \
        "https://nlp.stanford.edu/~wcmac/downloads/fracas.xml"
fi

# ── Create student accounts ──────────────────────────────
echo ""
echo "============================================"
echo "  Creating student accounts (student1-6)"
echo "============================================"
for i in $(seq 1 6); do
    username="student${i}"
    if ! id "$username" &>/dev/null; then
        sudo useradd -m -s /bin/bash "$username"
        echo "${username}:nestor2026" | sudo chpasswd
        sudo usermod -aG sudo "$username"
        echo "  Created $username (password: nestor2026)"
    else
        echo "  $username already exists"
    fi
    # Give access to nestor workspace
    sudo ln -sf /opt/nestor "/home/${username}/nestor" 2>/dev/null || true
    # Add opam env to their bashrc
    echo 'eval $(opam env --root /home/'$USER'/.opam)' | sudo tee -a "/home/${username}/.bashrc" > /dev/null
done

# ── Set API key placeholder ──────────────────────────────
echo ""
echo "  Add your Azure API key to /opt/nestor/.env:"
echo "  echo 'export AZURE_API_KEY=your-key' > /opt/nestor/.env"
if [ ! -f "/opt/nestor/.env" ]; then
    echo '# Add your API keys here' > /opt/nestor/.env
    echo 'export AZURE_API_KEY=""' >> /opt/nestor/.env
    echo 'export AZURE_OPENAI_ENDPOINT=""' >> /opt/nestor/.env
fi

# ── Verify ───────────────────────────────────────────────
echo ""
echo "============================================"
echo "  Verification"
echo "============================================"
echo -n "  prover9:  "; prover9 --version 2>&1 | head -1 || echo "MISSING"
echo -n "  mace4:    "; mace4 --version 2>&1 | head -1 || echo "MISSING"
echo -n "  eprover:  "; eprover --version 2>&1 | head -1 || echo "MISSING"
echo -n "  coqc:     "; coqc --version 2>&1 | head -1 || echo "MISSING"
echo -n "  python3:  "; python3 --version
echo -n "  fracas:   "; [ -f /opt/nestor/data/fracas.xml ] && echo "OK" || echo "MISSING"

echo ""
echo "============================================"
echo "  DONE. Now:"
echo "  1. Put your API key in /opt/nestor/.env"
echo "  2. Copy the skill_nli-fol-prover/ folder to /opt/nestor/"
echo "  3. Copy demo.py to /opt/nestor/"
echo "  4. Tell students to SSH in and run:"
echo "     cd ~/nestor && source .env && python3 demo.py"
echo "============================================"

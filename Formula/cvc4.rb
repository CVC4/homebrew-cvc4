class Cvc4 < Formula
  include Language::Python::Virtualenv

  desc "Open-source automatic theorem prover for SMT"
  homepage "https://cvc4.cs.stanford.edu/"
  url "https://github.com/CVC4/CVC4/archive/1.8.tar.gz"
  sha256 "27de80c14e1c5f9e2aa4ea75566fd0b7ff2093247516d725fa22c599a6b9bf37"
  head "https://github.com/CVC4/CVC4.git"

  option "with-java-bindings", "Compile with Java bindings"
  option "with-gpl", "Allow building against GPL'ed libraries"

  depends_on "coreutils" => :build
  depends_on "cmake" => :build
  depends_on "python" => :build
  depends_on "gmp"
  depends_on "readline" => :optional
  depends_on :java if build.with? "java-bindings"
  depends_on "swig"
  depends_on "automake" => :build if not build.head?
  depends_on "libtool" => :build if not build.head?
  depends_on "cryptominisat" => :build
  depends_on :arch => :x86_64

  resource "toml" do
    url "https://files.pythonhosted.org/packages/da/24/84d5c108e818ca294efe7c1ce237b42118643ce58a14d2462b3b2e3800d5/toml-0.10.1.tar.gz"
    sha256 "926b612be1e5ce0634a2ca03470f95169cf16f939018233a670519cb4ac58b0f"
  end

  def run_in_venv(venv, cmd)
    activate = Shellwords.join(["source", "#{venv}/bin/activate"])
    cmd_str = Shellwords.join(cmd)
    system "bash", "-c", (activate + " && " + cmd_str)
  end

  def install
    system "contrib/get-antlr-3.4"
    system "contrib/get-symfpu"

    args = ["--prefix=#{prefix}",
            "--symfpu",
            "--cryptominisat"]

    venv_root = "#{buildpath}/venv"
    if build.head?
      venv = virtualenv_create(venv_root, "python3")
      venv.pip_install resources
    else
      args << "--python3"
    end

    if build.with? "java-bindings"
      args << "--language-bindings=java"
    end

    if allow_gpl?
      args << "--gpl"
    end

    if build.with? "readline"
      gpl_dependency "readline"
      args << "--readline"
    end

    if build.head?
      run_in_venv(venv_root, ["./configure.sh", *args])
      chdir "build" do
        run_in_venv(venv_root, ["make", "install"])
      end
    else
      system "./configure.sh", *args
      chdir "build" do
        system "make", "install"
      end
    end
  end

  test do
    (testpath/"simple.cvc").write <<~EOS
      x0, x1, x2, x3 : BOOLEAN;
      ASSERT x1 OR NOT x0;
      ASSERT x0 OR NOT x3;
      ASSERT x3 OR x2;
      ASSERT x1 AND NOT x1;
      % EXPECT: valid
      QUERY x2;
    EOS
    result = shell_output "#{bin}/cvc4 #{(testpath/"simple.cvc")}"
    assert_match /valid/, result
    (testpath/"simple.smt").write <<~EOS
      (set-option :produce-models true)
      (set-logic QF_BV)
      (define-fun s_2 () Bool false)
      (define-fun s_1 () Bool true)
      (assert (not s_1))
      (check-sat)
    EOS
    result = shell_output "#{bin}/cvc4 --lang smt #{(testpath/"simple.smt")}"
    assert_match /unsat/, result
  end

  private

  def allow_gpl?
    build.with?("gpl")
  end

  def gpl_dependency(dep)
    odie "--with-gpl is required to build with #{dep}" unless allow_gpl?
  end
end

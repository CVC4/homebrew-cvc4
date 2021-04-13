class Cvc4 < Formula
  include Language::Python::Virtualenv

  desc "Open-source automatic theorem prover for SMT"
  homepage "https://cvc4.cs.stanford.edu/"
  url "https://github.com/CVC4/CVC4/archive/1.8.tar.gz"
  sha256 "27de80c14e1c5f9e2aa4ea75566fd0b7ff2093247516d725fa22c599a6b9bf37"
  head "https://github.com/CVC4/CVC4.git"

  option "with-java-bindings", "Compile with Java bindings"
  option "with-gpl", "Allow building against GPL'ed libraries"

  depends_on "cmake" => :build
  depends_on "coreutils" => :build
  depends_on "cryptominisat" => :build
  depends_on "python" => :build
  depends_on arch: :x86_64 unless build.head?
  depends_on "gmp"
  depends_on :java if build.with? "java-bindings"
  depends_on "swig"
  depends_on "readline" => :optional

  resource "toml" do
    url "https://files.pythonhosted.org/packages/b9/19/5cbd78eac8b1783671c40e34bb0fa83133a06d340a38b55c645076d40094/toml-0.10.0.tar.gz"
    sha256 "229f81c57791a41d65e399fc06bf0848bab550a9dfd5ed66df18ce5f05e73d5c"
  end

  def run_with_prefix_path(prefix_path, cmd)
    cmd_str = Shellwords.join(cmd)
    system "bash", "-c", "export \"CMAKE_PREFIX_PATH=#{prefix_path}:\$CMAKE_PREFIX_PATH\"; #{cmd_str}"
  end

  def install
    system "contrib/get-antlr-3.4" unless build.head?
    system "contrib/get-symfpu" unless build.head?

    venv_root = "#{buildpath}/venv"
    venv = virtualenv_create(venv_root, "python3")
    venv.pip_install resources

    args = ["--prefix=#{prefix}",
            "--symfpu",
            "--cryptominisat"]

    args << "--python3" unless build.head?
    args << "--language-bindings=java" if build.with? "java-bindings"
    args << "--gpl" if allow_gpl?

    if build.with? "readline"
      gpl_dependency "readline"
      args << "--readline"
    end

    run_with_prefix_path("#{venv_root}/bin", ["./configure.sh", *args])
    chdir "build" do
      system "make", "install"
    end
  end

  test do
    (testpath/"simple.cvc").write <<~EOS
      x0, x1, x2, x3 : BOOLEAN;
      ASSERT x1 OR NOT x0;
      ASSERT x0 OR NOT x3;
      ASSERT x3 OR x2;
      ASSERT x1 AND NOT x1;
      % EXPECT: entailed
      QUERY x2;
    EOS
    result = shell_output "#{bin}/cvc4 #{testpath/"simple.cvc"}"
    assert_match(/entailed/, result)
    (testpath/"simple.smt").write <<~EOS
      (set-option :produce-models true)
      (set-logic QF_BV)
      (define-fun s_2 () Bool false)
      (define-fun s_1 () Bool true)
      (assert (not s_1))
      (check-sat)
    EOS
    result = shell_output "#{bin}/cvc4 --lang smt #{testpath/"simple.smt"}"
    assert_match(/unsat/, result)
  end

  private

  def allow_gpl?
    build.with?("gpl")
  end

  def gpl_dependency(dep)
    odie "--with-gpl is required to build with #{dep}" unless allow_gpl?
  end
end

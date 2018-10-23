class Cryptominisat < Formula
  desc "An advanced SAT solver"
  homepage "https://www.msoos.org/"
  url "https://github.com/msoos/cryptominisat/archive/5.6.5.tar.gz"
  sha256 "b2751f8380a59c4885bea4c297536f0af2230306b1458d3e6b78d6e29f37b9d2"

  depends_on "cmake" => :build
  depends_on "python" => :recommended
  depends_on :arch => :x86_64

  def install
    mkdir "build" do
      system "cmake", "-DCMAKE_INSTALL_PREFIX=#{prefix}", "-DNOM4RI=ON", ".."
      system "make", "install"
    end
  end
end

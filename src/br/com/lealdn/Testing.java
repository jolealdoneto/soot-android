package br.com.lealdn;

public class Testing {

	public void doNothing() {
		int i = 0;
		i += 1;
		if (i > 0) {
			System.currentTimeMillis();
			if (i < 2) {
				System.out.println("ok");
			}
			else {
				System.out.println("nein");
			}
		}
		else {
			System.out.println("Hello");
		}
	}

}
